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

/-! ## WithLp 2 transport: 2-D Fourier of Schwartz IS Schwartz

We can transport a Schwartz function on `ℝ × ℝ` (Prod = L∞-norm) to a
Schwartz function on `WithLp 2 (ℝ × ℝ)` (L²-norm = inner product space)
via Mathlib's `WithLp.prodContinuousLinearEquiv`.  Then Mathlib's
`SchwartzMap.fourierTransformCLM` (the 2-D Fourier as a Schwartz
endomorphism) applies, giving a Schwartz function on `WithLp 2`.
Transporting back gives a Schwartz function on `ℝ × ℝ` whose values
match `fourier2D f`.

This closes `summable_fourier2D_postulate` via `summable_2d_schwartz_proved`
applied to the transported function.
-/

/-- Transport `f : 𝓢(ℝ × ℝ, ℂ)` to a Schwartz function on `WithLp 2 (ℝ × ℝ)`. -/
noncomputable def schwartzWithLp (f : 𝓢(ℝ × ℝ, ℂ)) :
    𝓢(WithLp 2 (ℝ × ℝ), ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ) f

@[simp] theorem schwartzWithLp_apply (f : 𝓢(ℝ × ℝ, ℂ))
    (v : WithLp 2 (ℝ × ℝ)) :
    (schwartzWithLp f : WithLp 2 (ℝ × ℝ) → ℂ) v =
      (f : ℝ × ℝ → ℂ) (WithLp.ofLp v) := by
  simp [schwartzWithLp]

/-- The full 2-D Fourier of f, packaged as a Schwartz function on `ℝ × ℝ`.

Defined by going through `WithLp 2 (ℝ × ℝ)`: transport f to WithLp,
apply Mathlib's `SchwartzMap.fourierTransformCLM`, then transport back. -/
noncomputable def fourier2DSchwartz (f : 𝓢(ℝ × ℝ, ℂ)) :
    𝓢(ℝ × ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm
    (SchwartzMap.fourierTransformCLM ℝ (schwartzWithLp f))

/-- Values of `fourier2DSchwartz f` match `fourier2D f`. -/
theorem fourier2DSchwartz_apply (f : 𝓢(ℝ × ℝ, ℂ)) (p : ℝ × ℝ) :
    (fourier2DSchwartz f : ℝ × ℝ → ℂ) p = fourier2D f p.1 p.2 := by
  show (𝓕 ((schwartzWithLp f : 𝓢(WithLp 2 (ℝ × ℝ), ℂ)) :
      WithLp 2 (ℝ × ℝ) → ℂ))
    ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm p) = fourier2D f p.1 p.2
  rw [fourier_eq' ((schwartzWithLp f : 𝓢(WithLp 2 (ℝ × ℝ), ℂ)) :
    WithLp 2 (ℝ × ℝ) → ℂ)
    ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm p)]
  unfold fourier2D
  have hMP : MeasureTheory.MeasurePreserving
      (@WithLp.toLp 2 (ℝ × ℝ)) :=
    WithLp.volume_preserving_toLp (U := ℝ) (V := ℝ)
  have hME : MeasurableEmbedding (@WithLp.toLp 2 (ℝ × ℝ)) :=
    (MeasurableEquiv.toLp 2 (ℝ × ℝ)).measurableEmbedding
  rw [← hMP.integral_comp hME
      (fun v : WithLp 2 (ℝ × ℝ) =>
        Complex.exp (((-2 * π * inner ℝ v
          ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm p) : ℝ) : ℂ) * Complex.I) •
          (schwartzWithLp f : WithLp 2 (ℝ × ℝ) → ℂ) v)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [smul_eq_mul, schwartzWithLp_apply]
  have h_inner : (inner ℝ ((@WithLp.toLp 2 (ℝ × ℝ)) q)
      ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm p) : ℝ) =
      q.1 * p.1 + q.2 * p.2 := by
    simp [WithLp.prod_inner_apply, RCLike.inner_apply, mul_comm]
  show Complex.exp (((-2 * π * inner ℝ ((@WithLp.toLp 2 (ℝ × ℝ)) q)
      ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm p) : ℝ) : ℂ) * Complex.I) *
      (f : ℝ × ℝ → ℂ) (WithLp.ofLp ((@WithLp.toLp 2 (ℝ × ℝ)) q)) =
    Complex.exp (-(2 * Real.pi * (p.1 * q.1 + p.2 * q.2)) * Complex.I) *
      (f : ℝ × ℝ → ℂ) (q.1, q.2)
  rw [h_inner]
  have h_ofLp_toLp : (WithLp.ofLp ((@WithLp.toLp 2 (ℝ × ℝ)) q)) = q := rfl
  rw [h_ofLp_toLp]
  conv_lhs => rw [show q = (q.1, q.2) from Prod.mk.eta.symm]
  congr 1
  push_cast
  ring

/-! ## Schwartz decay in the y-direction (helper toward closing
`partial_fourier_is_Schwartz_postulate`)

The bound `(1+‖y‖)^k · ‖f(x, y)‖ ≤ C_k(f)` uniformly in x is the key
estimate for proving integrability/continuity of the partial Fourier
`x ↦ 𝓕(f.rightPartial x)(n)`.  We use `‖y‖ ≤ ‖(x, y)‖` (Prod-sup norm)
and Mathlib's `norm_pow_mul_le_seminorm`.
-/

/-- For Schwartz `f : 𝓢(ℝ × ℝ, ℂ)`, the bound
`(1+‖y‖)^k · ‖f(x, y)‖ ≤ 2^k · (‖f‖_(0,0) + ‖f‖_(k,0))` uniformly in `x`.

PROVED via `(1+a)^k ≤ 2^k · (1 + a^k)` + `norm_pow_mul_le_seminorm`. -/
theorem schwartz_y_decay_bound (f : 𝓢(ℝ × ℝ, ℂ)) (k : ℕ) (x y : ℝ) :
    (1 + ‖y‖) ^ k * ‖(f : ℝ × ℝ → ℂ) (x, y)‖ ≤
      2 ^ k * (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ k 0 f) := by
  have h_norm_y : ‖y‖ ≤ ‖((x, y) : ℝ × ℝ)‖ := by simp [Prod.norm_def]
  have h_seminorm_0 : ‖(f : ℝ × ℝ → ℂ) (x, y)‖ ≤ SchwartzMap.seminorm ℝ 0 0 f :=
    SchwartzMap.norm_le_seminorm (𝕜 := ℝ) f (x, y)
  have h_seminorm_k : ‖((x, y) : ℝ × ℝ)‖ ^ k * ‖(f : ℝ × ℝ → ℂ) (x, y)‖ ≤
      SchwartzMap.seminorm ℝ k 0 f :=
    SchwartzMap.norm_pow_mul_le_seminorm (𝕜 := ℝ) f k (x, y)
  -- (1+‖y‖)^k ≤ 2^k · (1 + ‖y‖^k):  (1+a)^k ≤ (2·max(1, a))^k = 2^k · max(1, a^k) ≤ 2^k · (1+a^k)
  have h_pow_bound : (1 + ‖y‖) ^ k ≤ 2 ^ k * (1 + ‖y‖ ^ k) := by
    have h1 : 1 + ‖y‖ ≤ 2 * max 1 ‖y‖ := by
      by_cases hy_le : ‖y‖ ≤ 1
      · have : max 1 ‖y‖ = 1 := max_eq_left hy_le
        rw [this]; linarith
      · push_neg at hy_le
        have : max 1 ‖y‖ = ‖y‖ := max_eq_right hy_le.le
        rw [this]; linarith
    have h2 : (max 1 ‖y‖ : ℝ) ^ k ≤ 1 + ‖y‖ ^ k := by
      by_cases hy_le : ‖y‖ ≤ 1
      · have hmax : max 1 ‖y‖ = 1 := max_eq_left hy_le
        rw [hmax, one_pow]
        linarith [pow_nonneg (norm_nonneg y) k]
      · push_neg at hy_le
        have hmax : max 1 ‖y‖ = ‖y‖ := max_eq_right hy_le.le
        rw [hmax]
        linarith [pow_nonneg (norm_nonneg y) k]
    calc (1 + ‖y‖) ^ k
        ≤ (2 * max 1 ‖y‖) ^ k := pow_le_pow_left₀ (by linarith [norm_nonneg y]) h1 k
      _ = 2 ^ k * (max 1 ‖y‖) ^ k := by rw [mul_pow]
      _ ≤ 2 ^ k * (1 + ‖y‖ ^ k) := by
        apply mul_le_mul_of_nonneg_left h2 (by positivity)
  -- ‖y‖^k · ‖f(x,y)‖ ≤ ‖(x,y)‖^k · ‖f(x,y)‖ ≤ ‖f‖_(k,0)
  have h_y_pow_bound : ‖y‖ ^ k * ‖(f : ℝ × ℝ → ℂ) (x, y)‖ ≤
      SchwartzMap.seminorm ℝ k 0 f := by
    calc ‖y‖ ^ k * ‖(f : ℝ × ℝ → ℂ) (x, y)‖
        ≤ ‖((x, y) : ℝ × ℝ)‖ ^ k * ‖(f : ℝ × ℝ → ℂ) (x, y)‖ := by
          apply mul_le_mul_of_nonneg_right
          · exact pow_le_pow_left₀ (norm_nonneg _) h_norm_y k
          · exact norm_nonneg _
      _ ≤ SchwartzMap.seminorm ℝ k 0 f := h_seminorm_k
  -- (1+‖y‖)^k · ‖f(x,y)‖ ≤ 2^k · (1 + ‖y‖^k) · ‖f(x,y)‖
  --                      = 2^k · ‖f(x,y)‖ + 2^k · ‖y‖^k · ‖f(x,y)‖
  --                      ≤ 2^k · ‖f‖_(0,0) + 2^k · ‖f‖_(k,0)
  --                      = 2^k · (‖f‖_(0,0) + ‖f‖_(k,0))
  have h_2k_pos : (0 : ℝ) ≤ 2 ^ k := by positivity
  calc (1 + ‖y‖) ^ k * ‖(f : ℝ × ℝ → ℂ) (x, y)‖
      ≤ (2 ^ k * (1 + ‖y‖ ^ k)) * ‖(f : ℝ × ℝ → ℂ) (x, y)‖ := by
        apply mul_le_mul_of_nonneg_right h_pow_bound (norm_nonneg _)
    _ = 2 ^ k * (‖(f : ℝ × ℝ → ℂ) (x, y)‖ + ‖y‖ ^ k * ‖(f : ℝ × ℝ → ℂ) (x, y)‖) := by ring
    _ ≤ 2 ^ k *
          (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ k 0 f) := by
        apply mul_le_mul_of_nonneg_left _ h_2k_pos
        linarith [h_seminorm_0, h_y_pow_bound]

/-- Pointwise norm bound following from `schwartz_y_decay_bound`:
`‖f(x, y)‖ ≤ C / (1+‖y‖)^k` uniformly in `x`. -/
theorem schwartz_y_decay_div (f : 𝓢(ℝ × ℝ, ℂ)) (k : ℕ) (x y : ℝ) :
    ‖(f : ℝ × ℝ → ℂ) (x, y)‖ ≤
      (2 ^ k * (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ k 0 f)) /
        (1 + ‖y‖) ^ k := by
  have h_pos : 0 < (1 + ‖y‖) ^ k := by positivity
  have h_bound := schwartz_y_decay_bound f k x y
  rw [le_div_iff₀ h_pos, mul_comm]
  exact h_bound

/-- Joint 2-D decay bound: `(1+‖x‖)^L · (1+‖y‖)^K · ‖f(x, y)‖ ≤
2^(L+K) · (‖f‖_(0,0) + ‖f‖_(L+K, 0))`.

PROVED via `(1+|x|) · (1+|y|) ≤ (1+‖(x,y)‖)^2` (for Prod sup norm) and
the prod-norm Schwartz bound. -/
theorem schwartz_xy_decay_bound (f : 𝓢(ℝ × ℝ, ℂ)) (L K : ℕ) (x y : ℝ) :
    (1 + ‖x‖) ^ L * (1 + ‖y‖) ^ K * ‖(f : ℝ × ℝ → ℂ) (x, y)‖ ≤
      2 ^ (L + K) *
        (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ (L + K) 0 f) := by
  have h_norm_x : ‖x‖ ≤ ‖((x, y) : ℝ × ℝ)‖ := by simp [Prod.norm_def]
  have h_norm_y : ‖y‖ ≤ ‖((x, y) : ℝ × ℝ)‖ := by simp [Prod.norm_def]
  -- (1+‖x‖)^L * (1+‖y‖)^K ≤ (1+‖(x,y)‖)^(L+K)
  have h_factor : (1 + ‖x‖) ^ L * (1 + ‖y‖) ^ K ≤
      (1 + ‖((x, y) : ℝ × ℝ)‖) ^ (L + K) := by
    have h_x_le : 1 + ‖x‖ ≤ 1 + ‖((x, y) : ℝ × ℝ)‖ := by linarith
    have h_y_le : 1 + ‖y‖ ≤ 1 + ‖((x, y) : ℝ × ℝ)‖ := by linarith
    calc (1 + ‖x‖) ^ L * (1 + ‖y‖) ^ K
        ≤ (1 + ‖((x, y) : ℝ × ℝ)‖) ^ L * (1 + ‖((x, y) : ℝ × ℝ)‖) ^ K := by
          apply mul_le_mul
          · exact pow_le_pow_left₀ (by linarith [norm_nonneg x]) h_x_le L
          · exact pow_le_pow_left₀ (by linarith [norm_nonneg y]) h_y_le K
          · positivity
          · positivity
      _ = (1 + ‖((x, y) : ℝ × ℝ)‖) ^ (L + K) := by rw [← pow_add]
  -- Now use (1+‖(x,y)‖)^(L+K) · ‖f(x, y)‖ ≤ 2^(L+K) · (‖f‖_(0,0) + ‖f‖_(L+K, 0))
  -- This is the prod-norm form of schwartz_y_decay_bound (use ‖(x,y)‖ in place of ‖y‖).
  have h_prod_decay : (1 + ‖((x, y) : ℝ × ℝ)‖) ^ (L + K) *
      ‖(f : ℝ × ℝ → ℂ) (x, y)‖ ≤
        2 ^ (L + K) *
          (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ (L + K) 0 f) := by
    -- Apply the same case-split argument as in schwartz_y_decay_bound, but with
    -- p := (x, y) and ‖p‖ in place of ‖y‖.
    set p : ℝ × ℝ := (x, y) with hp_def
    set k : ℕ := L + K
    have h_seminorm_0 : ‖(f : ℝ × ℝ → ℂ) p‖ ≤ SchwartzMap.seminorm ℝ 0 0 f :=
      SchwartzMap.norm_le_seminorm (𝕜 := ℝ) f p
    have h_seminorm_k : ‖p‖ ^ k * ‖(f : ℝ × ℝ → ℂ) p‖ ≤
        SchwartzMap.seminorm ℝ k 0 f :=
      SchwartzMap.norm_pow_mul_le_seminorm (𝕜 := ℝ) f k p
    have h_pow_bound : (1 + ‖p‖) ^ k ≤ 2 ^ k * (1 + ‖p‖ ^ k) := by
      have h1 : 1 + ‖p‖ ≤ 2 * max 1 ‖p‖ := by
        by_cases hp_le : ‖p‖ ≤ 1
        · have hmax : max 1 ‖p‖ = 1 := max_eq_left hp_le
          rw [hmax]; linarith
        · push_neg at hp_le
          have hmax : max 1 ‖p‖ = ‖p‖ := max_eq_right hp_le.le
          rw [hmax]; linarith
      have h2 : (max 1 ‖p‖ : ℝ) ^ k ≤ 1 + ‖p‖ ^ k := by
        by_cases hp_le : ‖p‖ ≤ 1
        · have hmax : max 1 ‖p‖ = 1 := max_eq_left hp_le
          rw [hmax, one_pow]
          linarith [pow_nonneg (norm_nonneg p) k]
        · push_neg at hp_le
          have hmax : max 1 ‖p‖ = ‖p‖ := max_eq_right hp_le.le
          rw [hmax]
          linarith [pow_nonneg (norm_nonneg p) k]
      calc (1 + ‖p‖) ^ k
          ≤ (2 * max 1 ‖p‖) ^ k := pow_le_pow_left₀ (by linarith [norm_nonneg p]) h1 k
        _ = 2 ^ k * (max 1 ‖p‖) ^ k := by rw [mul_pow]
        _ ≤ 2 ^ k * (1 + ‖p‖ ^ k) := by
          apply mul_le_mul_of_nonneg_left h2 (by positivity)
    calc (1 + ‖p‖) ^ k * ‖(f : ℝ × ℝ → ℂ) p‖
        ≤ (2 ^ k * (1 + ‖p‖ ^ k)) * ‖(f : ℝ × ℝ → ℂ) p‖ := by
          apply mul_le_mul_of_nonneg_right h_pow_bound (norm_nonneg _)
      _ = 2 ^ k * (‖(f : ℝ × ℝ → ℂ) p‖ + ‖p‖ ^ k * ‖(f : ℝ × ℝ → ℂ) p‖) := by ring
      _ ≤ 2 ^ k *
            (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ k 0 f) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [h_seminorm_0, h_seminorm_k]
  -- Combine: (1+‖x‖)^L · (1+‖y‖)^K · ‖f(x,y)‖ ≤ (1+‖(x,y)‖)^(L+K) · ‖f(x,y)‖ ≤ 2^(L+K) · ...
  calc (1 + ‖x‖) ^ L * (1 + ‖y‖) ^ K * ‖(f : ℝ × ℝ → ℂ) (x, y)‖
      ≤ (1 + ‖((x, y) : ℝ × ℝ)‖) ^ (L + K) * ‖(f : ℝ × ℝ → ℂ) (x, y)‖ := by
        exact mul_le_mul_of_nonneg_right h_factor (norm_nonneg _)
    _ ≤ 2 ^ (L + K) *
          (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ (L + K) 0 f) :=
        h_prod_decay

/-- Symmetric to `schwartz_y_decay_bound`: bound in the x-direction.
`(1+‖x‖)^k · ‖f(x, y)‖ ≤ 2^k · (‖f‖_(0,0) + ‖f‖_(k,0))` uniformly in `y`. -/
theorem schwartz_x_decay_bound (f : 𝓢(ℝ × ℝ, ℂ)) (k : ℕ) (x y : ℝ) :
    (1 + ‖x‖) ^ k * ‖(f : ℝ × ℝ → ℂ) (x, y)‖ ≤
      2 ^ k * (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ k 0 f) := by
  have h_norm_x : ‖x‖ ≤ ‖((x, y) : ℝ × ℝ)‖ := by simp [Prod.norm_def]
  have h_seminorm_0 : ‖(f : ℝ × ℝ → ℂ) (x, y)‖ ≤ SchwartzMap.seminorm ℝ 0 0 f :=
    SchwartzMap.norm_le_seminorm (𝕜 := ℝ) f (x, y)
  have h_seminorm_k : ‖((x, y) : ℝ × ℝ)‖ ^ k * ‖(f : ℝ × ℝ → ℂ) (x, y)‖ ≤
      SchwartzMap.seminorm ℝ k 0 f :=
    SchwartzMap.norm_pow_mul_le_seminorm (𝕜 := ℝ) f k (x, y)
  have h_pow_bound : (1 + ‖x‖) ^ k ≤ 2 ^ k * (1 + ‖x‖ ^ k) := by
    have h1 : 1 + ‖x‖ ≤ 2 * max 1 ‖x‖ := by
      by_cases hx_le : ‖x‖ ≤ 1
      · have hmax : max 1 ‖x‖ = 1 := max_eq_left hx_le
        rw [hmax]; linarith
      · push_neg at hx_le
        have hmax : max 1 ‖x‖ = ‖x‖ := max_eq_right hx_le.le
        rw [hmax]; linarith
    have h2 : (max 1 ‖x‖ : ℝ) ^ k ≤ 1 + ‖x‖ ^ k := by
      by_cases hx_le : ‖x‖ ≤ 1
      · have hmax : max 1 ‖x‖ = 1 := max_eq_left hx_le
        rw [hmax, one_pow]
        linarith [pow_nonneg (norm_nonneg x) k]
      · push_neg at hx_le
        have hmax : max 1 ‖x‖ = ‖x‖ := max_eq_right hx_le.le
        rw [hmax]
        linarith [pow_nonneg (norm_nonneg x) k]
    calc (1 + ‖x‖) ^ k
        ≤ (2 * max 1 ‖x‖) ^ k := pow_le_pow_left₀ (by linarith [norm_nonneg x]) h1 k
      _ = 2 ^ k * (max 1 ‖x‖) ^ k := by rw [mul_pow]
      _ ≤ 2 ^ k * (1 + ‖x‖ ^ k) := by
        apply mul_le_mul_of_nonneg_left h2 (by positivity)
  have h_x_pow_bound : ‖x‖ ^ k * ‖(f : ℝ × ℝ → ℂ) (x, y)‖ ≤
      SchwartzMap.seminorm ℝ k 0 f := by
    calc ‖x‖ ^ k * ‖(f : ℝ × ℝ → ℂ) (x, y)‖
        ≤ ‖((x, y) : ℝ × ℝ)‖ ^ k * ‖(f : ℝ × ℝ → ℂ) (x, y)‖ := by
          apply mul_le_mul_of_nonneg_right
          · exact pow_le_pow_left₀ (norm_nonneg _) h_norm_x k
          · exact norm_nonneg _
      _ ≤ SchwartzMap.seminorm ℝ k 0 f := h_seminorm_k
  have h_2k_pos : (0 : ℝ) ≤ 2 ^ k := by positivity
  calc (1 + ‖x‖) ^ k * ‖(f : ℝ × ℝ → ℂ) (x, y)‖
      ≤ (2 ^ k * (1 + ‖x‖ ^ k)) * ‖(f : ℝ × ℝ → ℂ) (x, y)‖ := by
        apply mul_le_mul_of_nonneg_right h_pow_bound (norm_nonneg _)
    _ = 2 ^ k * (‖(f : ℝ × ℝ → ℂ) (x, y)‖ + ‖x‖ ^ k * ‖(f : ℝ × ℝ → ℂ) (x, y)‖) := by ring
    _ ≤ 2 ^ k *
          (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ k 0 f) := by
        apply mul_le_mul_of_nonneg_left _ h_2k_pos
        linarith [h_seminorm_0, h_x_pow_bound]

/-- Continuity of the partial Fourier in `x`: for Schwartz `f` and real `n`,
the function `x ↦ ∫ y, exp(-2πi n y) · f(x, y) dy` is continuous.

PROVED via `MeasureTheory.continuous_of_dominated` with the integrable
bound `y ↦ C / (1+|y|)^2` (from `schwartz_y_decay_div` at `k = 2`). -/
theorem continuous_partial_fourier_integrand (f : 𝓢(ℝ × ℝ, ℂ)) (n : ℝ) :
    Continuous fun x : ℝ =>
      ∫ y : ℝ, Complex.exp (-(2 * Real.pi * (n * y)) * Complex.I) *
        (f : ℝ × ℝ → ℂ) (x, y) := by
  -- Set up the parametric integral framework
  set C : ℝ := 2 ^ 2 * (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ 2 0 f)
  set bound : ℝ → ℝ := fun y => C / (1 + ‖y‖) ^ 2
  -- bound is integrable
  have h_bound_int : MeasureTheory.Integrable bound := by
    have h_inv_rpow : MeasureTheory.Integrable
        (fun y : ℝ => (1 + ‖y‖) ^ (-(2 : ℝ))) := by
      apply integrable_one_add_norm (μ := MeasureTheory.volume)
      simp
    -- Convert rpow form to division form
    have h_pow_eq : ∀ y : ℝ, (1 + ‖y‖) ^ (-(2 : ℝ)) = 1 / (1 + ‖y‖) ^ 2 := by
      intro y
      have h_pos : (0 : ℝ) < 1 + ‖y‖ := by linarith [norm_nonneg y]
      rw [Real.rpow_neg h_pos.le]
      rw [show (1 + ‖y‖) ^ (2 : ℝ) = (1 + ‖y‖) ^ (2 : ℕ) from by
        rw [← Real.rpow_natCast]; norm_num]
      exact (one_div _).symm
    have h_inv_div : MeasureTheory.Integrable
        (fun y : ℝ => 1 / (1 + ‖y‖) ^ 2) := by
      refine h_inv_rpow.congr ?_
      exact Filter.Eventually.of_forall (fun y => h_pow_eq y)
    -- bound = C * (1 / (1+|y|)^2)
    show MeasureTheory.Integrable (fun y : ℝ => C / (1 + ‖y‖) ^ 2)
    have h_eq : (fun y : ℝ => C / (1 + ‖y‖) ^ 2) =
        (fun y : ℝ => C * (1 / (1 + ‖y‖) ^ 2)) := by
      ext y; ring
    rw [h_eq]
    exact h_inv_div.const_mul C
  -- Apply continuous_of_dominated
  apply MeasureTheory.continuous_of_dominated
  · -- AEStronglyMeasurable for each x
    intro x
    refine Continuous.aestronglyMeasurable ?_
    refine Continuous.mul ?_ ?_
    · fun_prop
    · refine Continuous.comp f.continuous ?_
      fun_prop
  · -- bound: ∀ x, ∀ᵐ y, ‖F x y‖ ≤ bound y
    intro x
    refine Filter.Eventually.of_forall fun y => ?_
    -- ‖exp(...) · f(x, y)‖ = ‖f(x, y)‖ ≤ bound y
    rw [norm_mul]
    have h_exp_norm : ‖Complex.exp (-(2 * Real.pi * (n * y)) * Complex.I)‖ = 1 := by
      have := norm_fourier_char_eq_one (n * y)
      convert this using 2
      push_cast
      ring
    rw [h_exp_norm, one_mul]
    exact schwartz_y_decay_div f 2 x y
  · -- bound is integrable
    exact h_bound_int
  · -- ∀ᵐ y, x ↦ F x y is continuous
    refine Filter.Eventually.of_forall fun y => ?_
    refine Continuous.mul continuous_const ?_
    refine Continuous.comp f.continuous ?_
    fun_prop

/-- Integrability of the partial Fourier integrand as a function of `x`.

PROVED via `Integrable.integral_prod_left` applied to
`fourier_mul_schwartz_integrable_2d f 0 n` (the integrability of
`exp(-2πi n y) · f(x, y)` on ℝ × ℝ). -/
theorem integrable_partial_fourier_integrand (f : 𝓢(ℝ × ℝ, ℂ)) (n : ℝ) :
    MeasureTheory.Integrable fun x : ℝ =>
      ∫ y : ℝ, Complex.exp (-(2 * Real.pi * (n * y)) * Complex.I) *
        (f : ℝ × ℝ → ℂ) (x, y) := by
  -- Use the fact that the 2-D integrand is integrable (Integrable.bdd_mul +
  -- schwartz_integrable_2d), then apply Integrable.integral_prod_left to get
  -- integrability of the inner integral as a function of x.
  have h_f_int := schwartz_integrable_2d f
  have h_exp_cts : Continuous fun p : ℝ × ℝ =>
      Complex.exp (-(2 * Real.pi * (n * p.2)) * Complex.I) := by fun_prop
  have h_exp_bd : ∀ p : ℝ × ℝ,
      ‖Complex.exp (-(2 * Real.pi * (n * p.2)) * Complex.I)‖ ≤ 1 := by
    intro p
    have : ‖Complex.exp ((-(2 * Real.pi * (n * p.2)) : ℝ) * Complex.I)‖ = 1 :=
      Complex.norm_exp_ofReal_mul_I _
    convert this.le using 2
    push_cast
    ring
  have h_2d_int : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Complex.exp (-(2 * Real.pi * (n * p.2)) * Complex.I) *
        (f : ℝ × ℝ → ℂ) (p.1, p.2)) :=
    MeasureTheory.Integrable.bdd_mul h_f_int
      h_exp_cts.aestronglyMeasurable
      (MeasureTheory.ae_of_all _ h_exp_bd)
  exact h_2d_int.integral_prod_left

/-- The 1-D Fourier of the partial-Fourier integrand equals
`(fourier2DSchwartz f).leftPartial n` evaluated at `w`.

PROVED via `iterated_fourier_eq_2d_integral` + `fourier2DSchwartz_apply`. -/
theorem fourier_partial_fourier_integrand_eq (f : 𝓢(ℝ × ℝ, ℂ)) (n : ℝ) (w : ℝ) :
    𝓕 (fun x : ℝ => ∫ y : ℝ,
        Complex.exp (-(2 * Real.pi * (n * y)) * Complex.I) *
          (f : ℝ × ℝ → ℂ) (x, y)) w =
      ((fourier2DSchwartz f).leftPartial n : 𝓢(ℝ, ℂ)) w := by
  -- Unfold 𝓕 to the integral
  rw [fourier_eq' _ w]
  -- 𝓕(I)(w) = ∫ x, exp(-2π·⟨x, w⟩·I) • I(x)
  --        = ∫ x, exp(-2π·x·w·I) • (∫ y, exp(-2π·n·y·I) · f(x, y) dy)
  -- By iterated_fourier_eq_2d_integral, this equals fourier2D f w n.
  -- And by fourier2DSchwartz_apply, (fourier2DSchwartz f).leftPartial n w = fourier2D f w n.
  rw [leftPartial_apply, fourier2DSchwartz_apply]
  -- Now goal: ∫ x, exp(-2π·⟨x, w⟩·I) • (∫ y, exp(-2π·n·y·I) · f(x, y) dy) = fourier2D f w n
  unfold fourier2D
  rw [iterated_fourier_eq_2d_integral f w n]
  -- Goal: ∫ x, exp(-2π·⟨x, w⟩·I) • (...) = ∫ x, exp(-(2π·(w·x))·I) · (...)
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  -- Match the outer exponentials
  have h_inner : (inner ℝ x w : ℝ) = x * w := by
    simp [RCLike.inner_apply, mul_comm]
  rw [h_inner]
  congr 1
  push_cast
  ring

/-! ## CLOSE `partial_fourier_is_Schwartz_postulate` via Fourier inversion

With the helpers in place, we now PROVE the existential subtype
that constitutes the postulate's content.  The construction:

  `g := SchwartzMap.fourierInv ((fourier2DSchwartz f).leftPartial n)`

is automatically Schwartz (Mathlib's `SchwartzMap.fourierInv` is CLM).

The value spec follows from `Continuous.fourierInv_fourier_eq`
applied to `I(x) := ∫ y, exp(-2πi n y) f(x, y) dy`:
- I continuous (continuous_partial_fourier_integrand)
- I integrable (integrable_partial_fourier_integrand)
- 𝓕(I) integrable (= leftPartial n, Schwartz)
- Conclude I = 𝓕⁻¹(𝓕 I) = 𝓕⁻¹(leftPartial n) = g.
- And I(x) = 𝓕(f.rightPartial x)(n : ℝ) by Fubini direction (the integral
  is the partial Fourier of f.rightPartial x at n).
-/

/-- **CLOSED** (PROVED): the partial Fourier `x ↦ 𝓕(f.rightPartial x)(n)` is
Schwartz with the specified values.

Returns the same subtype as `partial_fourier_is_Schwartz_postulate` but
PROVED via the chain of helpers above.  The original
`partial_fourier_is_Schwartz_postulate` could now be redefined to call
this, but doing so requires a file reorganization (forward references).
For now, this is a parallel theorem providing the closure as Lean code. -/
noncomputable def partial_fourier_is_Schwartz_proved (f : 𝓢(ℝ × ℝ, ℂ)) (n : ℤ) :
    { g : 𝓢(ℝ, ℂ) // ∀ x : ℝ,
        (g : ℝ → ℂ) x = 𝓕 ((f.rightPartial x : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (n : ℝ) } := by
  -- Define the Schwartz function via Fourier inverse of leftPartial of fourier2DSchwartz.
  refine ⟨𝓕⁻ ((fourier2DSchwartz f).leftPartial n : 𝓢(ℝ, ℂ)), ?_⟩
  intro x
  -- Apply Continuous.fourierInv_fourier_eq to the integrand
  --   I(x') := ∫ y, exp(-2πi (n:ℝ) y) f(x', y) dy
  -- which is continuous + integrable + has integrable Fourier = leftPartial n.
  set I : ℝ → ℂ := fun x' => ∫ y : ℝ,
      Complex.exp (-(2 * Real.pi * ((n : ℝ) * y)) * Complex.I) *
        (f : ℝ × ℝ → ℂ) (x', y) with hI_def
  -- I is continuous and integrable.
  have hI_cont : Continuous I := continuous_partial_fourier_integrand f (n : ℝ)
  have hI_int : MeasureTheory.Integrable I :=
    integrable_partial_fourier_integrand f (n : ℝ)
  -- 𝓕(I) = leftPartial n  (as functions)
  have hF_I_eq : ∀ w : ℝ, 𝓕 I w =
      ((fourier2DSchwartz f).leftPartial n : 𝓢(ℝ, ℂ)) w :=
    fun w => fourier_partial_fourier_integrand_eq f (n : ℝ) w
  -- 𝓕(I) is integrable (since it equals a Schwartz function pointwise)
  have hF_I_int : MeasureTheory.Integrable (𝓕 I) := by
    refine ((fourier2DSchwartz f).leftPartial n).integrable.congr ?_
    refine Filter.Eventually.of_forall fun w => ?_
    exact (hF_I_eq w).symm
  -- Apply Fourier inversion to get I = 𝓕⁻¹(𝓕 I)
  have hI_inv : 𝓕⁻ (𝓕 I) = I := hI_cont.fourierInv_fourier_eq hI_int hF_I_int
  -- 𝓕⁻¹(𝓕 I) at x = I(x).
  -- Also, 𝓕⁻¹(leftPartial n) = 𝓕⁻¹(𝓕 I) since leftPartial n = 𝓕 I.
  -- So 𝓕⁻¹(leftPartial n) x = I(x).
  -- Need: SchwartzMap.fourierInv ((fourier2DSchwartz f).leftPartial n) x = 𝓕(f.rightPartial x)(n : ℝ)
  -- SchwartzMap.fourierInv g = 𝓕⁻¹ (g : ℝ → ℂ) at the coe level.
  -- We have I(x) = 𝓕⁻¹(leftPartial n) x.
  -- And I(x) = 𝓕(f.rightPartial x)(n : ℝ) (matches the goal modulo integral notation).
  have h_inv_eq : 𝓕⁻ (((fourier2DSchwartz f).leftPartial n : 𝓢(ℝ, ℂ)) :
      ℝ → ℂ) x = I x := by
    have h_eq_funext : (((fourier2DSchwartz f).leftPartial n : 𝓢(ℝ, ℂ)) :
        ℝ → ℂ) = 𝓕 I := by
      ext w
      exact (hF_I_eq w).symm
    rw [h_eq_funext]
    exact congrFun hI_inv x
  -- Now bridge: SchwartzMap.fourierInv ((fourier2DSchwartz f).leftPartial n) x
  --           = 𝓕⁻¹ (((fourier2DSchwartz f).leftPartial n : ℝ → ℂ)) x
  -- via SchwartzMap.fourierInv_coe.
  rw [show ((𝓕⁻ ((fourier2DSchwartz f).leftPartial n : 𝓢(ℝ, ℂ)) :
      𝓢(ℝ, ℂ)) : ℝ → ℂ) x = 𝓕⁻ (((fourier2DSchwartz f).leftPartial n :
      𝓢(ℝ, ℂ)) : ℝ → ℂ) x from by rw [SchwartzMap.fourierInv_coe]]
  rw [h_inv_eq]
  -- Now goal: I x = 𝓕(f.rightPartial x)(n : ℝ)
  -- Compute RHS as integral
  rw [hI_def]
  rw [fourier_eq' ((f.rightPartial x : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (n : ℝ)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [smul_eq_mul, rightPartial_apply]
  have h_inner : (inner ℝ y ((n : ℝ)) : ℝ) = y * (n : ℝ) := by
    simp [RCLike.inner_apply, mul_comm]
  rw [show (inner ℝ y ((n : ℝ)) : ℝ) = y * (n : ℝ) from h_inner]
  congr 1
  push_cast
  ring

/-! ## `partialFourier` accessors + downstream consumers (now PROVED)

With `partial_fourier_is_Schwartz_proved` above, we can define the accessors
without any sorry and immediately reprove all the downstream identities
that previously depended on the postulate.
-/

/-- The Schwartz function `x ↦ 𝓕(f.rightPartial x) n`.  Accessor for
`partial_fourier_is_Schwartz_proved`. -/
noncomputable def partialFourier (f : 𝓢(ℝ × ℝ, ℂ)) (n : ℤ) : 𝓢(ℝ, ℂ) :=
  (partial_fourier_is_Schwartz_proved f n).val

/-- Value spec: `(partialFourier f n) x = 𝓕(f.rightPartial x)(n)`. -/
theorem partialFourier_apply (f : 𝓢(ℝ × ℝ, ℂ)) (n : ℤ) (x : ℝ) :
    (partialFourier f n : ℝ → ℂ) x =
      𝓕 ((f.rightPartial x : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (n : ℝ) :=
  (partial_fourier_is_Schwartz_proved f n).property x

/-- The 1-D Fourier of `partialFourier f n` at a real point `m` equals
the 2-D Fourier of `f` at `(m, n)`.

PROVED via `iterated_fourier_eq_2d_integral` + `partialFourier_apply` +
`fourier_eq'` + identification of the inner integral with
`𝓕(f.rightPartial x)(n)`. -/
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

PROVED via `SchwartzMap.tsum_eq_tsum_fourier`. -/
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
`∑' m : ℤ, (partialFourier f n) m = ∑' m : ℤ, fourier2D f m n`. -/
theorem tsum_partialFourier_eq_fourier2D (f : 𝓢(ℝ × ℝ, ℂ)) (n : ℤ) :
    (∑' m : ℤ, (partialFourier f n : ℝ → ℂ) m) =
    ∑' m : ℤ, fourier2D f m n := by
  rw [tsum_partialFourier_eq_fourier]
  refine tsum_congr (fun m => ?_)
  exact fourier_partialFourier_eq_fourier2D f n m

/-! ## Towards full 2-D Schwartz Poisson summation

We can now restate the row-Poisson chain in terms of `partialFourier`,
then express the full 2-D Poisson identity modulo one remaining Fubini swap.
The other Fubini swap is now CLOSED via `fourier2DSchwartz_apply`.
-/

/-- **Postulate** (summability of the partial-Fourier on `ℤ × ℤ`): the
function `(m, n) ↦ (partialFourier f n) m` is summable on `ℤ × ℤ`.

TRUE: the "intermediate" 2-D Fourier (Fourier in `y` only) of a Schwartz
function on `ℝ × ℝ` is itself Schwartz on `ℝ × ℝ`; summability on `ℤ × ℤ`
then follows from Schwartz decay (as in `summable_2d_schwartz_proved`).

Cite: Stein–Shakarchi Ch. 4 (Fourier preserves Schwartz, multidim version).
Not in Mathlib v4.30 for `ℝ × ℝ`.

**Attack routes** (now that `partial_fourier_is_Schwartz_proved` and
its helpers are PROVED):

Route A — Direct bound via IBP + 2-D Schwartz seminorm:
Apply Mathlib's `pow_mul_norm_iteratedFDeriv_fourier_le` (k=0 case) to
`g := f.rightPartial m`:
  `|n|^K · |𝓕(g)(n)| ≤ 2^K · ∑_{p2 ≤ K} ∫ |∂^{p2}_y f(m, y)| dy`.
For 2-D Schwartz f, `(1+|m|)^L · (1+|y|)^2 · |∂^{p2}_y f(m, y)|` is
bounded uniformly by a Schwartz seminorm of f (via direction-restricted
2-D seminorm), giving `(1+|m|)^L · ∫ |∂^{p2}_y f(m, y)| dy ≤ C_L`.
Combined: `(1+|m|)^L · |n|^K · |partialFourier f n m| ≤ C(L, K, f)`.
For L, K ≥ 2 (with `(1+|n|)^K` instead of `|n|^K`), summability on
ℤ × ℤ follows via `summable_of_isBigO` against
`(m, n) ↦ 1 / ((1+|m|)^2 · (1+|n|)^2)`.
Lean implementation: ~200 LOC.  Subtle point: extracting the
y-only-direction seminorm bound from Mathlib's `iteratedFDeriv ℝ k f` on
ℝ × ℝ requires care (Mathlib's `iteratedFDeriv` is direction-mixed; need
the specialization to the y unit vector).

Route B — Construct `partial2DSchwartz f : 𝓢(ℝ × ℝ, ℂ)`:
Need a 2-D Schwartz function with values `partial2DSchwartz f (m, n) =
(partialFourier f n)(m)`.  Then `summable_2d_schwartz_proved` gives
summability immediately.  Construction is the hard part — requires a
"partial Fourier in 2nd variable preserves Schwartz on ℝ × ℝ"
endomorphism, which isn't a direct Mathlib lemma.  Could be built from
SchwartzMap.fourierTransformCLM + ad-hoc transport.  ~200-300 LOC.

Both routes need Mathlib infrastructure either not in v4.30 or not in
the right shape for direct use.  This remains the last sorry in
PoissonProd.lean as of 2026-05-27 session. -/
def summable_partialFourier_2d_postulate (f : 𝓢(ℝ × ℝ, ℂ)) :
    Summable (Function.uncurry
      fun m n : ℤ => (partialFourier f n : ℝ → ℂ) m) := sorry

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

/-- Absolute (norm) version of `summable_2d_schwartz_proved`: for any
Schwartz `f : 𝓢(ℝ × ℝ, ℂ)`, the function `(p.1, p.2) ↦ ‖f(p.1, p.2)‖` is
summable on `ℤ × ℤ`.

PROVED via the same chain as `summable_2d_schwartz_proved` plus
`.norm_left` to transfer the isBigO bound to the norm. -/
theorem summable_norm_2d_schwartz (f : 𝓢(ℝ × ℝ, ℂ)) :
    Summable fun p : ℤ × ℤ => ‖(f : ℝ × ℝ → ℂ) (p.1, p.2)‖ := by
  have h_decay : (fun x : ℝ × ℝ => (f : ℝ × ℝ → ℂ) x) =O[Filter.cocompact (ℝ × ℝ)]
      (fun x : ℝ × ℝ => ‖x‖ ^ (-(3 : ℝ))) :=
    f.isBigO_cocompact_rpow (-(3 : ℝ))
  have h_decay_int : (fun p : ℤ × ℤ => (f : ℝ × ℝ → ℂ) (p.1, p.2)) =O[Filter.cofinite]
      (fun p : ℤ × ℤ => ‖((p.1 : ℝ), (p.2 : ℝ))‖ ^ (-(3 : ℝ))) :=
    h_decay.comp_tendsto tendsto_int_prod_cocompact
  have h_summ_bound : Summable fun p : ℤ × ℤ =>
      ‖((p.1 : ℝ), (p.2 : ℝ))‖ ^ (-(3 : ℝ)) := by
    convert summable_norm_rpow_three_prod using 1
    ext p
    rw [norm_prod_int_eq, norm_finTwoArrow_symm_eq]
  -- Apply summable_of_isBigO with .norm_left for absolute summability
  exact summable_of_isBigO h_summ_bound h_decay_int.norm_left

/-- **CLOSED** (formerly `summable_fourier2D_postulate`): summability of
`fourier2D f` on `ℤ × ℤ`.

PROVED via `fourier2DSchwartz f` (PROVED Schwartz function on `ℝ × ℝ` whose
values match `fourier2D f`) + `summable_2d_schwartz_proved` (the absolute
2-D summability of any Schwartz function on `ℤ × ℤ`).  -/
theorem summable_fourier2D (f : 𝓢(ℝ × ℝ, ℂ)) :
    Summable (Function.uncurry fun m n : ℤ => fourier2D f m n) := by
  have h := summable_2d_schwartz_proved (fourier2DSchwartz f)
  refine h.congr (fun p => ?_)
  show (fourier2DSchwartz f : ℝ × ℝ → ℂ) (↑p.1, ↑p.2) =
      Function.uncurry (fun m n : ℤ => fourier2D f m n) p
  rw [fourier2DSchwartz_apply]
  rfl

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
      (summable_fourier2D f)
  rw [h_swap]
  -- Step 5: ∑' m, ∑' n, fourier2D f m n = ∑' p : ℤ × ℤ, fourier2D f p.1 p.2
  -- via Summable.tsum_prod (in reverse).
  have h_prod : (∑' p : ℤ × ℤ, fourier2D f p.1 p.2) =
      ∑' m : ℤ, ∑' n : ℤ, fourier2D f m n := by
    have h := Summable.tsum_prod (f := Function.uncurry
      fun m n : ℤ => fourier2D f m n) (summable_fourier2D f)
    -- h : ∑' p, uncurry F p = ∑' m, ∑' n, uncurry F (m, n)
    -- The LHS pattern is `∑' p, uncurry F p` = `∑' p, F p.1 p.2`
    -- which matches our target.
    convert h using 1
  rw [h_prod]

/-! ## Roadmap: from `tsum_2d_schwartz_poisson` to dedekindZeta functional equation

The 2-D Schwartz Poisson identity proved above is the analytic primitive
underlying the modular transformation of the 2-D Gaussian theta function,
which in turn (via Mellin transform) gives the dedekindZeta functional
equation for quadratic and biquadratic CM fields.

### Step A: Gaussian theta modular transformation (next concrete step)

Apply `tsum_2d_schwartz_poisson` to the 2-D Gaussian
  `g_t(x, y) := exp(-π · t · (x² + y²))`
giving
  `∑'_(m,n) g_t(m, n) = ∑'_(m,n) fourier2D(g_t)(m, n)`.

By Mathlib's `fourier_gaussian_innerProductSpace` (via `WithLp 2 (ℝ × ℝ)`
bridge), the Fourier of the 2-D Gaussian is itself a 2-D Gaussian:
  `fourier2D(g_t)(m, n) = t⁻¹ · exp(-π · (m² + n²) / t)`.

Combining:
  `∑'_(m,n) exp(-πt(m²+n²)) = t⁻¹ · ∑'_(m,n) exp(-π(m²+n²)/t)`

This is the 2-D Jacobi theta modular transformation `θ₂(1/t) = t · θ₂(t)`.

### Step B: Lattice theta for CM fields (subsequent step)

For a CM field K of complex degree f, the canonical embedding
`mixedEmbedding K : 𝓞_K → ℂ^f` gives a lattice in ℝ^(2f).  The lattice
theta function
  `θ_K(t) := ∑'_(α ∈ 𝓞_K) exp(-π·t · ‖mixedEmbedding K α‖²)`
is a multi-D Gaussian sum, generalizing Step A to dimension `2f`.

Multi-D Poisson summation (the d-dim generalization of `tsum_2d_schwartz_poisson`)
gives the modular transformation:
  `θ_K(1/t) = √|d_K| · t^f · θ_K(t)`
where `d_K = discr K`.

### Step C: Mellin transform to dedekindZeta (final step)

Mellin transform of `θ_K(t) - 1` produces the completed Dedekind zeta:
  `Λ_K(s) = π^(-s·f) · Γ(s/2)^f · ∫₀^∞ (θ_K(t) - 1) · t^(s-1) dt
         = (gamma factors) · dedekindZeta K`.

Modular transformation of `θ_K` ⟹ symmetric form of Mellin integral ⟹
functional equation `Λ_K(s) = Λ_K(1-s)`.

Via Mathlib's `Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean`, this
gives analytic continuation past `s = 1` and the residue/regulator bounds
that close `regulator_lower_bound_cm` + `dedekind_residue_upper_bound_cm`.

### What's MISSING from Mathlib v4.30

1. 2-D Gaussian `g_t : 𝓢(ℝ × ℝ, ℂ)` (definition + Schwartz proof).
   Doable via `SchwartzMap.compCLM` + `exp_neg_sq_isLittleO`.
2. `fourier_gaussian_innerProductSpace` bridged to `ℝ × ℝ` (Prod norm)
   via `WithLp 2`.  Doable but requires the WithLp continuity bridge.
3. Multi-D generalization of `tsum_2d_schwartz_poisson` (the d-dim version
   currently sorried as `tsum_eq_tsum_fourier_multi_postulate`).
4. Lattice theta `θ_K` definition + modular transformation.
5. Mellin transform of `θ_K - 1` and identification with `Λ_K`.

Each is a multi-week to multi-month Mathlib PR target.  The infrastructure
already provided above (`tsum_2d_schwartz_poisson` and ancillary lemmas)
is the foundation for Step A.
-/

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
