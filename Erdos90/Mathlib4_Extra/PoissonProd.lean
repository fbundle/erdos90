/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Mathlib
import Erdos90.Mathlib4_Extra.SeparablePoisson2D

/-!
# Multi-dimensional Schwartz Poisson summation — statement + partial PROVED pieces

For `f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)` (Schwartz on `d`-dimensional Euclidean space),
the multi-dimensional Poisson summation formula is

  `∑' (n : Fin d → ℤ), f (Int.cast ∘ n) = ∑' (n : Fin d → ℤ), 𝓕f (Int.cast ∘ n)`

(where `𝓕f` is the multi-dimensional Fourier integral using
`Real.fourierIntegral` aka `VectorFourier.fourierIntegral` with `Real.fourierChar`).

## Why this matters for Erd46

This unlocks two of our four proof-path sorries simultaneously
(`regulator_lower_bound_cm` Friedman, `dedekind_residue_upper_bound_cm`
Louboutin) via the chain:

  multi-D Poisson summation
    ⟹ Theta function for number-field lattice has modular transformation
    ⟹ `dedekindZeta` has functional equation (via Mathlib's `AbstractFuncEq`)
    ⟹ Friedman regulator bound + Louboutin residue bound

This file CURRENTLY just states the goal.  Closing it requires:
1. The PROVED 1-D case (Mathlib has `SchwartzMap.tsum_eq_tsum_fourier`).
2. A "partial Schwartz" construction: for `f : 𝓢(Fin d → ℝ, ℂ)` and `i : Fin d`,
   the function `y ↦ f (Function.update x i y)` is Schwartz in `y`.
3. Fubini-style swap of `tsum` on `Fin d → ℤ` vs nested `tsum`s.
4. Identification of iterated 1-D Fourier with the multi-D Fourier integral.

Each step is doable from Mathlib v4.30 primitives but adds up to multi-week
formalization.

## What this file provides

* `tsum_eq_tsum_fourier_multi_postulate` — the statement, sorried.
* `partial_schwartz_inr` — partial Schwartz construction (PROVED for `d = 2`).

## References

- Mathlib `Mathlib/Analysis/Fourier/PoissonSummation.lean` — 1-D.
- Mathlib `Mathlib/Analysis/Fourier/AddCircleMulti.lean` — multivariate
  Fourier series on `UnitAddTorus d`.
- Loeffler–Stoll 2025 — the architectural template for L-function formalization.
-/

namespace SchwartzMap

open MeasureTheory Real Complex
open scoped FourierTransform SchwartzMap

universe u

/-! ## Partial Schwartz construction

For `f : 𝓢(ℝ × ℝ, ℂ)`, the partial function `y ↦ f(x_0, y)` is Schwartz.
This is the building block for iterating 1-D Poisson summation.
-/

/-- For a fixed `x_0 : ℝ`, the inclusion map `ι : ℝ → ℝ × ℝ, y ↦ (x_0, y)` is
an affine map and has temperate growth.

PROVED Lean. -/
theorem _root_.Function.HasTemperateGrowth.inr_partial (x_0 : ℝ) :
    Function.HasTemperateGrowth (fun y : ℝ => (x_0, y)) := by
  have h_const : Function.HasTemperateGrowth (fun _ : ℝ => (x_0, (0 : ℝ))) :=
    Function.HasTemperateGrowth.const _
  have h_lin : Function.HasTemperateGrowth (ContinuousLinearMap.inr ℝ ℝ ℝ) :=
    ContinuousLinearMap.hasTemperateGrowth _
  have h_sum : Function.HasTemperateGrowth
      (fun y : ℝ => (x_0, (0 : ℝ)) + (ContinuousLinearMap.inr ℝ ℝ ℝ y)) :=
    h_const.add h_lin
  convert h_sum using 1
  ext y
  · simp
  · simp [ContinuousLinearMap.inr]

/-- The "right partial" of a 2-D Schwartz function: for fixed `x_0 : ℝ`,
the function `y ↦ f(x_0, y)` is a Schwartz function on `ℝ`.

PROVED via `SchwartzMap.compCLM` applied to the affine inclusion. -/
noncomputable def rightPartial (f : 𝓢(ℝ × ℝ, ℂ)) (x_0 : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM (𝕜 := ℝ)
    (Function.HasTemperateGrowth.inr_partial x_0)
    ⟨1, 1, fun y => by
      -- ‖y‖ ≤ 1 * (1 + ‖(x_0, y)‖)^1
      have h : ‖y‖ ≤ ‖(x_0, y)‖ := by
        simp [Prod.norm_def]
      linarith⟩
    f

/-- Pointwise evaluation: `(f.rightPartial x_0) y = f (x_0, y)`. -/
@[simp] theorem rightPartial_apply (f : 𝓢(ℝ × ℝ, ℂ)) (x_0 y : ℝ) :
    f.rightPartial x_0 y = f (x_0, y) := by
  simp [rightPartial]

/-- For a fixed `y_0 : ℝ`, the inclusion map `ι : ℝ → ℝ × ℝ, x ↦ (x, y_0)` is
an affine map and has temperate growth. -/
theorem _root_.Function.HasTemperateGrowth.inl_partial (y_0 : ℝ) :
    Function.HasTemperateGrowth (fun x : ℝ => (x, y_0)) := by
  have h_const : Function.HasTemperateGrowth (fun _ : ℝ => ((0 : ℝ), y_0)) :=
    Function.HasTemperateGrowth.const _
  have h_lin : Function.HasTemperateGrowth (ContinuousLinearMap.inl ℝ ℝ ℝ) :=
    ContinuousLinearMap.hasTemperateGrowth _
  have h_sum : Function.HasTemperateGrowth
      (fun x : ℝ => ((0 : ℝ), y_0) + (ContinuousLinearMap.inl ℝ ℝ ℝ x)) :=
    h_const.add h_lin
  convert h_sum using 1
  ext x
  · simp [ContinuousLinearMap.inl]
  · simp

/-- The "left partial" of a 2-D Schwartz function: for fixed `y_0 : ℝ`,
the function `x ↦ f(x, y_0)` is a Schwartz function on `ℝ`.

PROVED via `SchwartzMap.compCLM`. -/
noncomputable def leftPartial (f : 𝓢(ℝ × ℝ, ℂ)) (y_0 : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM (𝕜 := ℝ)
    (Function.HasTemperateGrowth.inl_partial y_0)
    ⟨1, 1, fun x => by
      have h : ‖x‖ ≤ ‖(x, y_0)‖ := by
        simp [Prod.norm_def]
      linarith⟩
    f

/-- Pointwise evaluation: `(f.leftPartial y_0) x = f (x, y_0)`. -/
@[simp] theorem leftPartial_apply (f : 𝓢(ℝ × ℝ, ℂ)) (y_0 x : ℝ) :
    f.leftPartial y_0 x = f (x, y_0) := by
  simp [leftPartial]

/-! ## Iterated 1-D Poisson on partial Schwartz (PROVED, no sorry)

The 1-D Poisson summation applied to the partial Schwartz functions.
-/

/-- For each `x_0 : ℝ`, Poisson summation in the second variable:

  `∑' n : ℤ, f(x_0, n) = ∑' n : ℤ, 𝓕(f.rightPartial x_0) n`

PROVED via 1-D Schwartz Poisson applied to `f.rightPartial x_0`. -/
theorem tsum_rightPartial_eq_fourier (f : 𝓢(ℝ × ℝ, ℂ)) (x_0 : ℝ) :
    (∑' n : ℤ, (f : ℝ × ℝ → ℂ) (x_0, n)) =
    ∑' n : ℤ, 𝓕 ((f.rightPartial x_0 : 𝓢(ℝ, ℂ)) : ℝ → ℂ) n := by
  -- Switch LHS to use rightPartial form, then apply 1-D Poisson
  have h_lhs : (∑' n : ℤ, (f : ℝ × ℝ → ℂ) (x_0, n)) =
      ∑' n : ℤ, ((f.rightPartial x_0 : 𝓢(ℝ, ℂ)) : ℝ → ℂ) n := by
    refine tsum_congr (fun n => ?_)
    simp [rightPartial_apply]
  rw [h_lhs]
  -- Apply 1-D Schwartz Poisson at x = 0
  have h := SchwartzMap.tsum_eq_tsum_fourier (f.rightPartial x_0) 0
  simp only [zero_add] at h
  rw [h]
  refine tsum_congr (fun n => ?_)
  rw [show ((0 : ℝ) : UnitAddCircle) = (0 : UnitAddCircle) from by
    simp [QuotientAddGroup.mk_zero]]
  rw [fourier_eval_zero, mul_one]
  rfl

/-- Symmetric form for `leftPartial`: Poisson summation in the first variable. -/
theorem tsum_leftPartial_eq_fourier (f : 𝓢(ℝ × ℝ, ℂ)) (y_0 : ℝ) :
    (∑' n : ℤ, (f : ℝ × ℝ → ℂ) (n, y_0)) =
    ∑' n : ℤ, 𝓕 ((f.leftPartial y_0 : 𝓢(ℝ, ℂ)) : ℝ → ℂ) n := by
  have h_lhs : (∑' n : ℤ, (f : ℝ × ℝ → ℂ) (n, y_0)) =
      ∑' n : ℤ, ((f.leftPartial y_0 : 𝓢(ℝ, ℂ)) : ℝ → ℂ) n := by
    refine tsum_congr (fun n => ?_)
    simp [leftPartial_apply]
  rw [h_lhs]
  have h := SchwartzMap.tsum_eq_tsum_fourier (f.leftPartial y_0) 0
  simp only [zero_add] at h
  rw [h]
  refine tsum_congr (fun n => ?_)
  rw [show ((0 : ℝ) : UnitAddCircle) = (0 : UnitAddCircle) from by
    simp [QuotientAddGroup.mk_zero]]
  rw [fourier_eval_zero, mul_one]
  rfl

/-- **Iterated 1-D Poisson** on a 2-D Schwartz function (PROVED).

For `f : 𝓢(ℝ × ℝ, ℂ)`:
  `∑' m, ∑' n, f(m, n) = ∑' m, ∑' n, 𝓕(f.rightPartial m) n`

This is the FIRST iteration step in the 2-D Poisson proof.  PROVED by
applying `tsum_rightPartial_eq_fourier` at each `m`. -/
theorem tsum_tsum_rightPartial_eq_fourier (f : 𝓢(ℝ × ℝ, ℂ)) :
    (∑' m : ℤ, ∑' n : ℤ, (f : ℝ × ℝ → ℂ) (m, n)) =
    ∑' m : ℤ, ∑' n : ℤ, 𝓕 ((f.rightPartial m : 𝓢(ℝ, ℂ)) : ℝ → ℂ) n := by
  refine tsum_congr (fun m => ?_)
  exact tsum_rightPartial_eq_fourier f m

/-! ## Remaining steps (documented sorries)

The full 2-D Schwartz Poisson summation requires three more steps,
each a multi-day Lean formalization on its own:
-/

/-- **Step 2** (POSTULATED): for `f : 𝓢(ℝ × ℝ, ℂ)` and `n : ℤ`,
the function `x ↦ 𝓕(f.rightPartial x) n` is Schwartz in `x`, **with value
specification**.

Concretely: there exists a Schwartz function `g : 𝓢(ℝ, ℂ)` such that
`g x = 𝓕 (f.rightPartial x) (n : ℝ)` for every `x : ℝ`.

This bundles "partial Fourier preserves Schwartz" together with the value
equation, so callers can both apply 1-D Poisson to `g` and rewrite the
sum back into the original `f`-form.

Cite: Stein–Shakarchi *Fourier Analysis* Chapter 4.  Not in Mathlib v4.30. -/
def partial_fourier_is_Schwartz_postulate
    (f : 𝓢(ℝ × ℝ, ℂ)) (n : ℤ) :
    { g : 𝓢(ℝ, ℂ) // ∀ x : ℝ,
        (g : ℝ → ℂ) x = 𝓕 ((f.rightPartial x : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (n : ℝ) } := sorry

/-- The Schwartz function `x ↦ 𝓕(f.rightPartial x) n`.  Accessor for
`partial_fourier_is_Schwartz_postulate`. -/
noncomputable def partialFourier (f : 𝓢(ℝ × ℝ, ℂ)) (n : ℤ) : 𝓢(ℝ, ℂ) :=
  (partial_fourier_is_Schwartz_postulate f n).val

/-- Value spec: `(partialFourier f n) x = 𝓕(f.rightPartial x)(n)`. -/
theorem partialFourier_apply (f : 𝓢(ℝ × ℝ, ℂ)) (n : ℤ) (x : ℝ) :
    (partialFourier f n : ℝ → ℂ) x =
      𝓕 ((f.rightPartial x : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (n : ℝ) :=
  (partial_fourier_is_Schwartz_postulate f n).property x

-- **Step 3** (the iterated Fourier identity in explicit integral form):
-- For Schwartz `f : 𝓢(ℝ × ℝ, ℂ)` and `m, n : ℝ`:
--   `∫_{ℝ × ℝ} e^{-2πi(mx+ny)} f(x, y) d(x, y) = ∫_ℝ e^{-2πi m x} · 𝓕(f.rightPartial x)(n) dx`
-- This is Fubini-Tonelli for the bivariate exponential.

/-- The exponential character has norm 1: `‖exp(-(2π·r)·I)‖ = 1` for any real `r`.

PROVED Lean. -/
theorem norm_fourier_char_eq_one (r : ℝ) :
    ‖Complex.exp (-(2 * Real.pi * r) * Complex.I)‖ = 1 := by
  rw [show (-(2 * Real.pi * r) * Complex.I)
      = ((-(2 * Real.pi * r) : ℝ) : ℂ) * Complex.I from by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

-- (fourier_mul_schwartz_integrable_2d omitted: the Schwartz integrability
-- on `ℝ × ℝ` requires `volume.HasTemperateGrowth` which is not auto-inferred
-- for Prod measures.  Mathematically obvious but Lean-tricky.)

/-- Schwartz functions on `ℝ × ℝ` are integrable (Lebesgue, default volume).

PROVED Lean via `SchwartzMap.integrable` once the `volume.HasTemperateGrowth`
typeclass is in scope. -/
theorem schwartz_integrable_2d (f : 𝓢(ℝ × ℝ, ℂ)) :
    MeasureTheory.Integrable (f : ℝ × ℝ → ℂ) :=
  f.integrable

/-- The product `exp(-(2πi(mx+ny))) · f(x, y)` is integrable on `ℝ × ℝ` for
any Schwartz `f`.

PROVED Lean. -/
theorem fourier_mul_schwartz_integrable_2d (f : 𝓢(ℝ × ℝ, ℂ)) (m n : ℝ) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Complex.exp (-(2 * Real.pi * (m * p.1 + n * p.2)) * Complex.I) *
        (f : ℝ × ℝ → ℂ) (p.1, p.2)) := by
  have h_f_int := schwartz_integrable_2d f
  have h_exp_cts : Continuous fun p : ℝ × ℝ =>
      Complex.exp (-(2 * Real.pi * (m * p.1 + n * p.2)) * Complex.I) := by
    fun_prop
  have h_exp_bd : ∀ p : ℝ × ℝ,
      ‖Complex.exp (-(2 * Real.pi * (m * p.1 + n * p.2)) * Complex.I)‖ ≤ 1 := by
    intro p
    -- Reduce to Complex.norm_exp_ofReal_mul_I (norm of e^{i·r} = 1 for real r)
    have : ‖Complex.exp (((-(2 * Real.pi * (m * p.1 + n * p.2))) : ℝ) * Complex.I)‖ = 1 :=
      Complex.norm_exp_ofReal_mul_I _
    convert this.le using 2
    push_cast
    ring
  -- Apply bdd_mul: bounded multiplier times integrable = integrable
  refine MeasureTheory.Integrable.bdd_mul h_f_int
    h_exp_cts.aestronglyMeasurable
    (MeasureTheory.ae_of_all _ h_exp_bd)

theorem iterated_fourier_eq_2d_integral
    (f : 𝓢(ℝ × ℝ, ℂ)) (m n : ℝ) :
    ∫ p : ℝ × ℝ,
        Complex.exp (-(2 * Real.pi * (m * p.1 + n * p.2)) * Complex.I) *
          (f : ℝ × ℝ → ℂ) (p.1, p.2) =
      ∫ x : ℝ, Complex.exp (-(2 * Real.pi * (m * x)) * Complex.I) *
          (∫ y : ℝ, Complex.exp (-(2 * Real.pi * (n * y)) * Complex.I) *
              (f : ℝ × ℝ → ℂ) (x, y)) := by
  -- Step 1: F is integrable.
  have h_F_int := fourier_mul_schwartz_integrable_2d f m n
  -- Step 2: Apply Fubini (integral_prod) to get the iterated form.
  -- LHS = ∫_{p : ℝ × ℝ}, F(p) dp = ∫ x, ∫ y, F(x, y) dy dx
  rw [show (∫ p : ℝ × ℝ,
        Complex.exp (-(2 * Real.pi * (m * p.1 + n * p.2)) * Complex.I) *
          (f : ℝ × ℝ → ℂ) (p.1, p.2))
        = ∫ x : ℝ, ∫ y : ℝ,
            Complex.exp (-(2 * Real.pi * (m * x + n * y)) * Complex.I) *
              (f : ℝ × ℝ → ℂ) (x, y) from
      MeasureTheory.integral_prod _ h_F_int]
  -- Step 3: For each x, factor the inner integral.
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  -- Inner: ∫ y, exp(-2πi(mx + ny)) · f(x, y) = exp(-2πi m x) · ∫ y, exp(-2πi n y) · f(x, y)
  have h_factor : ∀ y : ℝ,
      Complex.exp (-(2 * Real.pi * (m * x + n * y)) * Complex.I) *
        (f : ℝ × ℝ → ℂ) (x, y) =
      Complex.exp (-(2 * Real.pi * (m * x)) * Complex.I) *
        (Complex.exp (-(2 * Real.pi * (n * y)) * Complex.I) *
          (f : ℝ × ℝ → ℂ) (x, y)) := by
    intro y
    rw [show (-(2 * Real.pi * (m * x + n * y)) * Complex.I) =
        (-(2 * Real.pi * (m * x)) * Complex.I) + (-(2 * Real.pi * (n * y)) * Complex.I)
        from by push_cast; ring,
      Complex.exp_add]
    ring
  -- Apply the factorization and pull out the constant
  simp_rw [h_factor]
  rw [MeasureTheory.integral_const_mul]

/-! ## 2-D Fourier integral and its identification with `𝓕(partialFourier)`

We package the 2-D Fourier integral as `fourier2D`, then prove that the
1-D Fourier of `partialFourier f n` evaluated at `(m : ℝ)` equals
`fourier2D f m n`.  This is the bridge from the iterated 1-D Fourier
identity to a single 2-D Fourier integral.
-/

/-- 2-D Fourier integral of a Schwartz function `f : 𝓢(ℝ × ℝ, ℂ)`:
`fourier2D f m n = ∫ p, exp(-2πi(m·p.1 + n·p.2)) · f(p) dp`.  -/
noncomputable def fourier2D (f : 𝓢(ℝ × ℝ, ℂ)) (m n : ℝ) : ℂ :=
  ∫ p : ℝ × ℝ,
      Complex.exp (-(2 * Real.pi * (m * p.1 + n * p.2)) * Complex.I) *
        (f : ℝ × ℝ → ℂ) (p.1, p.2)

/-- The 1-D Fourier of `partialFourier f n` at a real point `m` equals
the 2-D Fourier of `f` at `(m, n)`.

PROVED via `iterated_fourier_eq_2d_integral` + `partialFourier_apply` +
`fourier_eq'` + identification of the inner integral with
`𝓕(f.rightPartial x)(n)`.  Requires only the partial-Fourier value spec
(part of `partial_fourier_is_Schwartz_postulate`).  -/
theorem fourier_partialFourier_eq_fourier2D
    (f : 𝓢(ℝ × ℝ, ℂ)) (n : ℤ) (m : ℝ) :
    𝓕 ((partialFourier f n : 𝓢(ℝ, ℂ)) : ℝ → ℂ) m = fourier2D f m n := by
  -- Step 1: Rewrite the inner partial-Fourier value as an explicit integral.
  have h_inner : ∀ x : ℝ,
      𝓕 ((f.rightPartial x : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (n : ℝ) =
        ∫ y : ℝ,
          Complex.exp (-(2 * Real.pi * ((n : ℝ) * y)) * Complex.I) *
            (f : ℝ × ℝ → ℂ) (x, y) := by
    intro x
    rw [fourier_eq' ((f.rightPartial x : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (n : ℝ)]
    simp only [smul_eq_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [rightPartial_apply]
    congr 1
    have hinner : (inner ℝ y ((n : ℝ)) : ℝ) = y * (n : ℝ) := by
      simp [RCLike.inner_apply, mul_comm]
    rw [hinner]
    push_cast
    ring
  -- Step 2: Unfold the LHS Fourier; apply partialFourier_apply; apply h_inner.
  rw [fourier_eq' ((partialFourier f n : 𝓢(ℝ, ℂ)) : ℝ → ℂ) m]
  simp only [smul_eq_mul]
  simp_rw [partialFourier_apply, h_inner]
  -- Step 3: Unfold fourier2D and apply iterated_fourier_eq_2d_integral.
  unfold fourier2D
  rw [iterated_fourier_eq_2d_integral f m (n : ℝ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hinner : (inner ℝ x m : ℝ) = x * m := by
    simp [RCLike.inner_apply, mul_comm]
  -- Goal: cexp(↑(-2π·inner x m)·I) · (∫ y, …) = cexp(-2π·m·x·I) · (∫ y, …)
  -- The inner integrals match; just need to match outer exponentials.
  show (Complex.exp (((-2 * Real.pi * inner ℝ x m : ℝ)) * Complex.I)) *
      (∫ y : ℝ, Complex.exp (-(2 * Real.pi * ((n : ℝ) * y)) * Complex.I) *
        (f : ℝ × ℝ → ℂ) (x, y)) =
      Complex.exp (-(2 * Real.pi * (m * x)) * Complex.I) *
      (∫ y : ℝ, Complex.exp (-(2 * Real.pi * ((n : ℝ) * y)) * Complex.I) *
        (f : ℝ × ℝ → ℂ) (x, y))
  congr 1
  rw [hinner]
  push_cast
  ring

/-- 1-D Poisson summation applied to `partialFourier f n`:

`∑' m : ℤ, (partialFourier f n) m = ∑' m : ℤ, 𝓕(partialFourier f n) m`

PROVED via `SchwartzMap.tsum_eq_tsum_fourier`.  -/
theorem tsum_partialFourier_eq_fourier (f : 𝓢(ℝ × ℝ, ℂ)) (n : ℤ) :
    (∑' m : ℤ, (partialFourier f n : ℝ → ℂ) m) =
    ∑' m : ℤ, 𝓕 ((partialFourier f n : 𝓢(ℝ, ℂ)) : ℝ → ℂ) m := by
  have h := SchwartzMap.tsum_eq_tsum_fourier (partialFourier f n) 0
  simp only [zero_add] at h
  rw [h]
  refine tsum_congr (fun m => ?_)
  rw [show ((0 : ℝ) : UnitAddCircle) = (0 : UnitAddCircle) from by
    simp [QuotientAddGroup.mk_zero]]
  rw [fourier_eval_zero, mul_one]
  rfl

/-- 1-D Poisson on `partialFourier f n`, with the RHS expressed via `fourier2D`:

`∑' m : ℤ, (partialFourier f n) m = ∑' m : ℤ, fourier2D f m n`

PROVED by combining `tsum_partialFourier_eq_fourier` with
`fourier_partialFourier_eq_fourier2D`.  -/
theorem tsum_partialFourier_eq_fourier2D (f : 𝓢(ℝ × ℝ, ℂ)) (n : ℤ) :
    (∑' m : ℤ, (partialFourier f n : ℝ → ℂ) m) =
    ∑' m : ℤ, fourier2D f m n := by
  rw [tsum_partialFourier_eq_fourier]
  refine tsum_congr (fun m => ?_)
  exact fourier_partialFourier_eq_fourier2D f n m

/-! ## Towards full 2-D Schwartz Poisson summation

We can now restate the row-Poisson chain in terms of `partialFourier`,
then express the full 2-D Poisson identity modulo two Fubini swaps.
-/

/-- **Postulate** (summability of the partial-Fourier on `ℤ × ℤ`): the
function `(m, n) ↦ (partialFourier f n) m` is summable on `ℤ × ℤ`.

TRUE: the "intermediate" 2-D Fourier (Fourier in `y` only) of a Schwartz
function on `ℝ × ℝ` is itself Schwartz on `ℝ × ℝ`; summability on `ℤ × ℤ`
then follows from Schwartz decay (as in `summable_2d_schwartz_proved`).

Cite: Stein–Shakarchi Ch. 4 (Fourier preserves Schwartz, multidim version).
Not in Mathlib v4.30 for `ℝ × ℝ`. -/
def summable_partialFourier_2d_postulate (f : 𝓢(ℝ × ℝ, ℂ)) :
    Summable (Function.uncurry
      fun m n : ℤ => (partialFourier f n : ℝ → ℂ) m) := sorry

/-- **Postulate** (summability of `fourier2D` on `ℤ × ℤ`): the function
`(m, n) ↦ fourier2D f m n` is summable on `ℤ × ℤ`.

TRUE: the full 2-D Fourier of a Schwartz function on `ℝ × ℝ` is itself
Schwartz on `ℝ × ℝ` (Plancherel); summability on `ℤ × ℤ` follows from
Schwartz decay.

Cite: Stein–Shakarchi Ch. 4.  Not in Mathlib v4.30. -/
def summable_fourier2D_postulate (f : 𝓢(ℝ × ℝ, ℂ)) :
    Summable (Function.uncurry fun m n : ℤ => fourier2D f m n) := sorry

/-- Mathlib's `EisensteinSeries.summable_one_div_norm_rpow` applied to k=3:
the `‖·‖^(-3)` series is summable over `Fin 2 → ℤ`.

PROVED (just a wrapper). -/
theorem summable_norm_rpow_three :
    Summable fun (x : Fin 2 → ℤ) => (‖x‖ : ℝ) ^ (-(3 : ℝ)) :=
  EisensteinSeries.summable_one_div_norm_rpow (by norm_num : (2 : ℝ) < 3)

/-- Transferred to `ℤ × ℤ` via the canonical equivalence. -/
theorem summable_norm_rpow_three_prod :
    Summable fun (p : ℤ × ℤ) =>
      (‖(finTwoArrowEquiv ℤ).symm p‖ : ℝ) ^ (-(3 : ℝ)) :=
  (finTwoArrowEquiv ℤ).symm.summable_iff.mpr summable_norm_rpow_three

/-- Norm conversion: the Pi norm on `(finTwoArrowEquiv ℤ).symm p` equals the
max of natAbs of components.

PROVED Lean via `EisensteinSeries.norm_eq_max_natAbs`. -/
theorem norm_finTwoArrow_symm_eq (p : ℤ × ℤ) :
    (‖(finTwoArrowEquiv ℤ).symm p‖ : ℝ) = max (p.1.natAbs : ℝ) (p.2.natAbs : ℝ) := by
  rw [EisensteinSeries.norm_eq_max_natAbs]
  simp [finTwoArrowEquiv]

/-- The integer inclusion `ℤ × ℤ → ℝ × ℝ` sends cofinite to cocompact.

PROVED Lean via `Tendsto.prodMap_coprod` applied to the 1-D
`Int.tendsto_coe_cofinite`, combined with `Filter.coprod_cofinite` and
`Filter.coprod_cocompact`. -/
theorem tendsto_int_prod_cocompact :
    Filter.Tendsto (fun p : ℤ × ℤ => ((p.1 : ℝ), (p.2 : ℝ)))
      Filter.cofinite (Filter.cocompact (ℝ × ℝ)) := by
  show Filter.Tendsto (Prod.map ((↑) : ℤ → ℝ) ((↑) : ℤ → ℝ)) _ _
  rw [← Filter.coprod_cofinite, ← Filter.coprod_cocompact]
  exact Filter.Tendsto.prodMap_coprod Int.tendsto_coe_cofinite Int.tendsto_coe_cofinite

/-- Prod-norm = max of natAbs for integer pairs.

PROVED Lean. -/
theorem norm_prod_int_eq (p : ℤ × ℤ) :
    ‖((p.1 : ℝ), (p.2 : ℝ))‖ = max (p.1.natAbs : ℝ) (p.2.natAbs : ℝ) := by
  simp only [Prod.norm_def, Real.norm_eq_abs]
  have h1 : |(p.1 : ℝ)| = (p.1.natAbs : ℝ) := by
    rw [show |(p.1 : ℝ)| = ((|p.1| : ℤ) : ℝ) from by push_cast; rfl]
    congr 1
    exact_mod_cast p.1.abs_eq_natAbs
  have h2 : |(p.2 : ℝ)| = (p.2.natAbs : ℝ) := by
    rw [show |(p.2 : ℝ)| = ((|p.2| : ℤ) : ℝ) from by push_cast; rfl]
    congr 1
    exact_mod_cast p.2.abs_eq_natAbs
  rw [h1, h2]

/-- Combined: 2-D Schwartz Poisson summable on `ℤ × ℤ`, modulo the
`tendsto_int_prod_cocompact` postulate (which is easy but tedious).

PROVED Lean assembly chain (3 of 4 steps proved):
1. Get the Schwartz decay `f =O[cocompact (ℝ × ℝ)] ‖·‖^(-3)`.
2. Compose with `tendsto_int_prod_cocompact` to get the bound at cofinite.
3. Use the proved 2-D summability `summable_norm_rpow_three_prod`.
4. Apply `summable_of_isBigO`. -/
theorem summable_2d_schwartz_proved (f : 𝓢(ℝ × ℝ, ℂ)) :
    Summable fun p : ℤ × ℤ => (f : ℝ × ℝ → ℂ) (p.1, p.2) := by
  -- Step 1: Schwartz decay
  have h_decay : (fun x : ℝ × ℝ => (f : ℝ × ℝ → ℂ) x) =O[Filter.cocompact (ℝ × ℝ)]
      (fun x : ℝ × ℝ => ‖x‖ ^ (-(3 : ℝ))) :=
    f.isBigO_cocompact_rpow (-(3 : ℝ))
  -- Step 2: Compose with the integer inclusion
  have h_decay_int : (fun p : ℤ × ℤ => (f : ℝ × ℝ → ℂ) (p.1, p.2)) =O[Filter.cofinite]
      (fun p : ℤ × ℤ => ‖((p.1 : ℝ), (p.2 : ℝ))‖ ^ (-(3 : ℝ))) :=
    h_decay.comp_tendsto tendsto_int_prod_cocompact
  -- Step 3: Summability of the bound function via norm conversion +
  -- summable_norm_rpow_three_prod
  have h_summ_bound : Summable fun p : ℤ × ℤ =>
      ‖((p.1 : ℝ), (p.2 : ℝ))‖ ^ (-(3 : ℝ)) := by
    convert summable_norm_rpow_three_prod using 1
    ext p
    rw [norm_prod_int_eq, norm_finTwoArrow_symm_eq]
  -- Step 4: summable_of_isBigO
  exact summable_of_isBigO h_summ_bound h_decay_int

/-! ## Summability via partial summability (PROVED)

Even without the full 2-D summability above, we can prove summability of
each ROW via 1-D Schwartz Poisson — i.e., for each fixed `m`,
`Summable (fun n : ℤ => f(m, n))`.
-/

/-- For 2-D Schwartz `f` and any fixed `m : ℤ`, the row `n ↦ f(m, n)` is
summable on `ℤ`.

PROVED via 1-D Schwartz summability applied to `f.rightPartial m`. -/
theorem summable_row_schwartz (f : 𝓢(ℝ × ℝ, ℂ)) (m : ℤ) :
    Summable fun n : ℤ => (f : ℝ × ℝ → ℂ) (m, n) := by
  have h := SchwartzMap.summable_int (f.rightPartial m)
  -- h : Summable fun n : ℤ => (f.rightPartial m) n
  -- We need: Summable fun n => f (m, n)
  -- Use rightPartial_apply
  refine h.congr (fun n => ?_)
  simp [rightPartial_apply]

/-- For 2-D Schwartz `f` and any fixed `n : ℤ`, the column `m ↦ f(m, n)` is
summable on `ℤ`. -/
theorem summable_col_schwartz (f : 𝓢(ℝ × ℝ, ℂ)) (n : ℤ) :
    Summable fun m : ℤ => (f : ℝ × ℝ → ℂ) (m, n) := by
  have h := SchwartzMap.summable_int (f.leftPartial n)
  refine h.congr (fun m => ?_)
  simp [leftPartial_apply]

/-- Each row is **absolutely** summable. -/
theorem summable_norm_row_schwartz (f : 𝓢(ℝ × ℝ, ℂ)) (m : ℤ) :
    Summable fun n : ℤ => ‖(f : ℝ × ℝ → ℂ) (m, n)‖ := by
  have h := SchwartzMap.summable_norm_int (f.rightPartial m)
  refine h.congr (fun n => ?_)
  simp [rightPartial_apply]

/-- Each column is **absolutely** summable. -/
theorem summable_norm_col_schwartz (f : 𝓢(ℝ × ℝ, ℂ)) (n : ℤ) :
    Summable fun m : ℤ => ‖(f : ℝ × ℝ → ℂ) (m, n)‖ := by
  have h := SchwartzMap.summable_norm_int (f.leftPartial n)
  refine h.congr (fun m => ?_)
  simp [leftPartial_apply]

/-- **Fubini for `tsum`** applied to 2-D Schwartz (PROVED modulo
`summable_2d_schwartz`).

If `f` is absolutely summable on `ℤ × ℤ` (provable from Schwartz decay,
currently postulated), then:
  `∑' (p : ℤ × ℤ), f p = ∑' m, ∑' n, f (m, n)`. -/
theorem tsum_prod_eq_tsum_tsum
    (f : 𝓢(ℝ × ℝ, ℂ)) :
    (∑' p : ℤ × ℤ, (f : ℝ × ℝ → ℂ) (p.1, p.2)) =
    ∑' m : ℤ, ∑' n : ℤ, (f : ℝ × ℝ → ℂ) (m, n) := by
  have h_summ := summable_2d_schwartz_proved f
  have h_summ_uncurry : Summable (Function.uncurry
      fun m n : ℤ => (f : ℝ × ℝ → ℂ) (m, n)) := by
    convert h_summ using 1
  have h_row : ∀ m : ℤ, Summable fun n : ℤ => (f : ℝ × ℝ → ℂ) (m, n) :=
    summable_row_schwartz f
  -- Apply Summable.tsum_prod'
  rw [h_summ.tsum_prod' h_row]

/-- **Combined**: 2-D Poisson up to the partial-Fourier step (PROVED modulo
`summable_2d_schwartz`).

  `∑' (p : ℤ × ℤ), f p = ∑' m, ∑' n, 𝓕(f.rightPartial m) n`

PROVED Lean by combining `tsum_prod_eq_tsum_tsum` (Fubini, modulo
postulate) + `tsum_tsum_rightPartial_eq_fourier` (1-D Poisson per row,
fully PROVED).

To get the full 2-D Poisson on the RHS, the remaining steps are:
1. Show `m ↦ ∑' n, 𝓕(f.rightPartial m) n` is Schwartz in m (postulate 2).
2. Apply 1-D Poisson in m direction.
3. Identify with 2-D Fourier integral (postulate 3).
4. Use Fubini reverse to get tsum on ℤ × ℤ on the RHS. -/
theorem tsum_prod_eq_tsum_tsum_fourier_rightPartial
    (f : 𝓢(ℝ × ℝ, ℂ)) :
    (∑' p : ℤ × ℤ, (f : ℝ × ℝ → ℂ) (p.1, p.2)) =
    ∑' m : ℤ, ∑' n : ℤ, 𝓕 ((f.rightPartial m : 𝓢(ℝ, ℂ)) : ℝ → ℂ) n := by
  rw [tsum_prod_eq_tsum_tsum, tsum_tsum_rightPartial_eq_fourier]

-- (tsum_prod_eq_tsum_tsum_fourier_leftPartial omitted: the swap of tsum
-- ordering via Equiv.prodComm hits a Lean typeclass timeout.  Mathematically
-- straightforward but Lean-tricky.  The rightPartial form above suffices.)

/-! ## Full 2-D Schwartz Poisson summation (modulo 2 summability postulates)

We assemble the full 2-D Poisson identity
  `∑' p : ℤ × ℤ, f p = ∑' p : ℤ × ℤ, fourier2D f p.1 p.2`
modulo `partial_fourier_is_Schwartz_postulate` and the two summability
postulates `summable_partialFourier_2d_postulate` and
`summable_fourier2D_postulate`.
-/

/-- Rewrite of `tsum_prod_eq_tsum_tsum_fourier_rightPartial` via the
value spec of `partialFourier`:

`∑' p : ℤ × ℤ, f p = ∑' m, ∑' n, (partialFourier f n) m`

PROVED Lean using `partialFourier_apply`. -/
theorem tsum_prod_eq_tsum_tsum_partialFourier (f : 𝓢(ℝ × ℝ, ℂ)) :
    (∑' p : ℤ × ℤ, (f : ℝ × ℝ → ℂ) (p.1, p.2)) =
    ∑' m : ℤ, ∑' n : ℤ, (partialFourier f n : ℝ → ℂ) m := by
  rw [tsum_prod_eq_tsum_tsum_fourier_rightPartial]
  refine tsum_congr (fun m => ?_)
  refine tsum_congr (fun n => ?_)
  rw [partialFourier_apply]

/-- Swap the order of summation `∑' m, ∑' n` ↔ `∑' n, ∑' m` for the
partial-Fourier function, using `summable_partialFourier_2d_postulate`.

PROVED modulo `summable_partialFourier_2d_postulate` via `Summable.tsum_comm`.
-/
theorem tsum_tsum_partialFourier_swap (f : 𝓢(ℝ × ℝ, ℂ)) :
    (∑' m : ℤ, ∑' n : ℤ, (partialFourier f n : ℝ → ℂ) m) =
    ∑' n : ℤ, ∑' m : ℤ, (partialFourier f n : ℝ → ℂ) m :=
  (Summable.tsum_comm (f := fun m n : ℤ =>
    (partialFourier f n : ℝ → ℂ) m) (summable_partialFourier_2d_postulate f)).symm

/-- **Full 2-D Schwartz Poisson summation** (PROVED modulo 3 postulates):

`∑' p : ℤ × ℤ, f p = ∑' p : ℤ × ℤ, fourier2D f p.1 p.2`

Postulates consumed:
1. `partial_fourier_is_Schwartz_postulate` (Schwartz preservation + value spec)
2. `summable_partialFourier_2d_postulate`
3. `summable_fourier2D_postulate`

All three are TRUE Mathlib gaps with clear citations.  -/
theorem tsum_2d_schwartz_poisson (f : 𝓢(ℝ × ℝ, ℂ)) :
    (∑' p : ℤ × ℤ, (f : ℝ × ℝ → ℂ) (p.1, p.2)) =
    ∑' p : ℤ × ℤ, fourier2D f p.1 p.2 := by
  -- Step 1: LHS = ∑' m, ∑' n, (partialFourier f n) m  (PROVED above)
  rw [tsum_prod_eq_tsum_tsum_partialFourier]
  -- Step 2: swap to ∑' n, ∑' m  (Fubini, uses summable_partialFourier_2d_postulate)
  rw [tsum_tsum_partialFourier_swap]
  -- Step 3: ∑' n, ∑' m, (partialFourier f n) m = ∑' n, ∑' m, fourier2D f m n
  -- (via tsum_partialFourier_eq_fourier2D per n).
  conv_lhs => rw [show (∑' n : ℤ, ∑' m : ℤ, (partialFourier f n : ℝ → ℂ) m) =
      ∑' n : ℤ, ∑' m : ℤ, fourier2D f m n from by
    refine tsum_congr (fun n => ?_)
    exact tsum_partialFourier_eq_fourier2D f n]
  -- Step 4: swap ∑' n, ∑' m, fourier2D f m n = ∑' m, ∑' n, fourier2D f m n
  -- (Fubini, uses summable_fourier2D_postulate + Summable.tsum_comm)
  have h_swap : (∑' n : ℤ, ∑' m : ℤ, fourier2D f m n) =
      ∑' m : ℤ, ∑' n : ℤ, fourier2D f m n :=
    Summable.tsum_comm (f := fun m n : ℤ => fourier2D f m n)
      (summable_fourier2D_postulate f)
  rw [h_swap]
  -- Step 5: ∑' m, ∑' n, fourier2D f m n = ∑' p : ℤ × ℤ, fourier2D f p.1 p.2
  -- via Summable.tsum_prod (in reverse).
  have h_prod : (∑' p : ℤ × ℤ, fourier2D f p.1 p.2) =
      ∑' m : ℤ, ∑' n : ℤ, fourier2D f m n := by
    have h := Summable.tsum_prod (f := Function.uncurry
      fun m n : ℤ => fourier2D f m n) (summable_fourier2D_postulate f)
    -- h : ∑' p, uncurry F p = ∑' m, ∑' n, uncurry F (m, n)
    -- The LHS pattern is `∑' p, uncurry F p` = `∑' p, F p.1 p.2`
    -- which matches our target.
    convert h using 1
  rw [h_prod]

/-! ## Schwartz seminorm bound on partial Schwartz

The `rightPartial` of a 2-D Schwartz function has Schwartz seminorms
controlled by the 2-D Schwartz seminorms.  This is the key analytic fact
underlying `partial_fourier_is_Schwartz`.
-/

/-- Pointwise bound: `‖f(x_0, y)‖ ≤ ‖f‖_(0, 0)` (L^∞ bound).

PROVED Lean via Mathlib's `SchwartzMap.le_seminorm` at (0, 0). -/
theorem rightPartial_apply_norm_le (f : 𝓢(ℝ × ℝ, ℂ)) (x_0 y : ℝ) :
    ‖(f : ℝ × ℝ → ℂ) (x_0, y)‖ ≤ SchwartzMap.seminorm ℝ 0 0 f := by
  have := f.le_seminorm (𝕜 := ℝ) 0 0 (x_0, y)
  simpa using this

/-- Polynomial bound: `‖(x_0, y)‖^k · ‖f(x_0, y)‖ ≤ ‖f‖_(k, 0)`.

PROVED Lean via `SchwartzMap.le_seminorm` at (k, 0). -/
theorem rightPartial_apply_polynomial_le (f : 𝓢(ℝ × ℝ, ℂ)) (k : ℕ) (x_0 y : ℝ) :
    ‖((x_0, y) : ℝ × ℝ)‖ ^ k * ‖(f : ℝ × ℝ → ℂ) (x_0, y)‖ ≤
      SchwartzMap.seminorm ℝ k 0 f := by
  have := f.le_seminorm (𝕜 := ℝ) k 0 (x_0, y)
  simpa using this

/-- The y-variable bound: `‖y‖^k · ‖(f.rightPartial x_0)(y)‖ ≤ ‖f‖_(k, 0)`.

PROVED via the polynomial bound + `‖(x_0, y)‖ ≥ ‖y‖` (sup norm). -/
theorem rightPartial_seminorm_y_le (f : 𝓢(ℝ × ℝ, ℂ)) (k : ℕ) (x_0 y : ℝ) :
    ‖y‖ ^ k * ‖(f.rightPartial x_0 : 𝓢(ℝ, ℂ)) y‖ ≤
      SchwartzMap.seminorm ℝ k 0 f := by
  rw [rightPartial_apply]
  have h_bound := rightPartial_apply_polynomial_le f k x_0 y
  -- ‖(x_0, y)‖ ≥ ‖y‖ (sup norm on Prod)
  have h_norm : ‖y‖ ≤ ‖((x_0, y) : ℝ × ℝ)‖ := by
    simp [Prod.norm_def]
  calc ‖y‖ ^ k * ‖f (x_0, y)‖
      ≤ ‖((x_0, y) : ℝ × ℝ)‖ ^ k * ‖f (x_0, y)‖ := by
        apply mul_le_mul_of_nonneg_right
        · exact pow_le_pow_left₀ (norm_nonneg _) h_norm k
        · exact norm_nonneg _
    _ ≤ SchwartzMap.seminorm ℝ k 0 f := h_bound

/-- The x-variable bound: `‖x_0‖^k · ‖(f.rightPartial x_0)(y)‖ ≤ ‖f‖_(k, 0)`.

PROVED via the polynomial bound + `‖(x_0, y)‖ ≥ ‖x_0‖` (sup norm). -/
theorem rightPartial_seminorm_x_le (f : 𝓢(ℝ × ℝ, ℂ)) (k : ℕ) (x_0 y : ℝ) :
    ‖x_0‖ ^ k * ‖(f.rightPartial x_0 : 𝓢(ℝ, ℂ)) y‖ ≤
      SchwartzMap.seminorm ℝ k 0 f := by
  rw [rightPartial_apply]
  have h_bound := rightPartial_apply_polynomial_le f k x_0 y
  have h_norm : ‖x_0‖ ≤ ‖((x_0, y) : ℝ × ℝ)‖ := by
    simp [Prod.norm_def]
  calc ‖x_0‖ ^ k * ‖f (x_0, y)‖
      ≤ ‖((x_0, y) : ℝ × ℝ)‖ ^ k * ‖f (x_0, y)‖ := by
        apply mul_le_mul_of_nonneg_right
        · exact pow_le_pow_left₀ (norm_nonneg _) h_norm k
        · exact norm_nonneg _
    _ ≤ SchwartzMap.seminorm ℝ k 0 f := h_bound

/-- Combined: `‖x_0‖^k · ‖y‖^k · ‖f(x_0, y)‖ ≤ (‖f‖_(2k, 0))`.

Via the product bound `‖x_0‖^k · ‖y‖^k ≤ ‖(x_0, y)‖^(2k)` (using
`‖(x_0, y)‖^2 = max(‖x_0‖, ‖y‖)² ≥ ‖x_0‖ · ‖y‖`). -/
theorem rightPartial_seminorm_xy_le (f : 𝓢(ℝ × ℝ, ℂ)) (k : ℕ) (x_0 y : ℝ) :
    ‖x_0‖ ^ k * ‖y‖ ^ k * ‖(f.rightPartial x_0 : 𝓢(ℝ, ℂ)) y‖ ≤
      SchwartzMap.seminorm ℝ (2 * k) 0 f := by
  rw [rightPartial_apply]
  have h_bound := rightPartial_apply_polynomial_le f (2 * k) x_0 y
  -- ‖(x_0, y)‖^(2k) ≥ ‖x_0‖^k · ‖y‖^k
  have h_norm : ‖x_0‖ ^ k * ‖y‖ ^ k ≤ ‖((x_0, y) : ℝ × ℝ)‖ ^ (2 * k) := by
    rw [two_mul, pow_add]
    apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg _)
      (by simp [Prod.norm_def] : ‖x_0‖ ≤ _) k)
      (pow_le_pow_left₀ (norm_nonneg _)
        (by simp [Prod.norm_def] : ‖y‖ ≤ _) k)
      (by positivity) (by positivity)
  calc ‖x_0‖ ^ k * ‖y‖ ^ k * ‖f (x_0, y)‖
      ≤ ‖((x_0, y) : ℝ × ℝ)‖ ^ (2 * k) * ‖f (x_0, y)‖ := by
        apply mul_le_mul_of_nonneg_right h_norm (norm_nonneg _)
    _ ≤ SchwartzMap.seminorm ℝ (2 * k) 0 f := h_bound

/-! ## Multi-dim Poisson summation (currently sorried)

The statement uses `EuclideanSpace ℝ (Fin d)` which is `Fin d → ℝ` with
Euclidean inner product (the correct domain for the Fourier transform).
-/

/-- **Multi-dimensional Schwartz Poisson summation** (postulated).

For `f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)`, the sum of `f` over the integer
lattice `ℤ^d ⊆ ℝ^d` equals the sum of the Fourier transform `𝓕f` over the
same lattice.

This is the **load-bearing piece** for closing
`regulator_lower_bound_cm` + `dedekind_residue_upper_bound_cm` via the
`dedekindZeta` functional equation.

Cite: Tate's thesis; Stein–Shakarchi *Fourier Analysis* Chapter 4.
Not in Mathlib v4.30. -/
def tsum_eq_tsum_fourier_multi_postulate
    (d : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) :
    (∑' (n : Fin d → ℤ),
      (f : EuclideanSpace ℝ (Fin d) → ℂ)
        ((EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => (n i : ℝ)))) =
    (∑' (n : Fin d → ℤ),
      𝓕 (f : EuclideanSpace ℝ (Fin d) → ℂ)
        ((EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => (n i : ℝ)))) := sorry

end SchwartzMap
