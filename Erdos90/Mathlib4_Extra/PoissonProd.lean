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
the function `x ↦ 𝓕(f.rightPartial x) n` is Schwartz in `x`.

This is "partial Fourier preserves Schwartz".  Standard fact; requires
careful derivation in Lean using Schwartz seminorm bounds and the
smoothness/decay of `(x, y) ↦ 𝓕(f(x, ·))(y)`.

Cite: Stein–Shakarchi *Fourier Analysis* Chapter 4.  Not in Mathlib v4.30. -/
def partial_fourier_is_Schwartz_postulate
    (f : 𝓢(ℝ × ℝ, ℂ)) (n : ℤ) :
    𝓢(ℝ, ℂ) := sorry

/-- **Step 3** (POSTULATED): the iterated 1-D Fourier integral equals
the 2-D Fourier integral.

For `f : 𝓢(ℝ × ℝ, ℂ)`, `m, n : ℝ`:
  `𝓕(x ↦ 𝓕(f.rightPartial x) n)(m) = 𝓕(2-D) f (m, n)`

This is "Fubini for Fourier integrals" — requires careful integration
swapping with absolutely integrable bounds. -/
def iterated_fourier_eq_2d_postulate
    (f : 𝓢(ℝ × ℝ, ℂ)) (m n : ℝ) :
    ℂ := sorry

/-- **Step 4**: Summability of 2-D Schwartz on `ℤ × ℤ`.

For `f : 𝓢(ℝ × ℝ, ℂ)`, `Summable (fun p : ℤ × ℤ => f (p.1, p.2))`.

PARTIALLY PROVED: the underlying ingredients are PROVED (summable bound
+ Schwartz decay), but the norm conversion between
`‖(finTwoArrowEquiv ℤ).symm p‖` (Pi norm) and the Prod norm of `(p.1, p.2)`
requires explicit work in Lean.

Postulated for now; the underlying ingredients are documented. -/
def summable_2d_schwartz_postulate (f : 𝓢(ℝ × ℝ, ℂ)) :
    Summable fun p : ℤ × ℤ => (f : ℝ × ℝ → ℂ) (p.1, p.2) := sorry

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

POSTULATED for now.  The proof is straightforward (integer points in a
bounded region are finite) but requires careful bookkeeping with bounded
sets in `ℝ × ℝ`. -/
def tendsto_int_prod_cocompact :
    Filter.Tendsto (fun p : ℤ × ℤ => ((p.1 : ℝ), (p.2 : ℝ)))
      Filter.cofinite (Filter.cocompact (ℝ × ℝ)) := sorry

/-- Prod-norm = max of natAbs for integer pairs.

POSTULATED — the equality is true (both equal `max(|p.1|, |p.2|)`) but
the Lean proof requires careful manipulation of `Real.norm_eq_abs`,
`Int.cast_natAbs`, and `Prod.norm_def`. -/
def norm_prod_int_eq (p : ℤ × ℤ) :
    ‖((p.1 : ℝ), (p.2 : ℝ))‖ = max (p.1.natAbs : ℝ) (p.2.natAbs : ℝ) := sorry

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
  have h_summ := summable_2d_schwartz_postulate f
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
