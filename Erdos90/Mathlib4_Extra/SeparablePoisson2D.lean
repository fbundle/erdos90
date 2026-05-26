/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Mathlib

/-!
# Separable 2-D Poisson summation (Mathlib-PR draft)

For Schwartz functions `g, h : 𝓢(ℝ, ℂ)`, the 2-D Poisson summation formula
for the product function `f(x, y) = g(x) · h(y)` follows immediately from
the 1-D version by iteration.

This is a small building block toward general multi-D Poisson summation
(see `MultiDimPoisson.lean` for the documentation skeleton).

## Main results

* `SchwartzMap.tsum_product_eq_tsum_fourier_product` — the separable case.

## Limitations

This file only handles SEPARABLE Schwartz functions.  General multi-D
Poisson summation requires more sophisticated arguments (Fubini for tsum on
prod types, multi-D Fourier transform on inner product spaces, etc.).
-/

namespace SchwartzMap

open MeasureTheory Real Complex
open scoped FourierTransform

/-- 1-D Schwartz Poisson summation evaluated at `x = 0`:
`∑' n : ℤ, f n = ∑' n : ℤ, 𝓕 f n`. -/
lemma tsum_eq_tsum_fourier_zero (f : 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, (f : ℝ → ℂ) n) = ∑' n : ℤ, 𝓕 (f : ℝ → ℂ) n := by
  have h := SchwartzMap.tsum_eq_tsum_fourier f 0
  simp only [zero_add] at h
  rw [h]
  refine tsum_congr (fun n => ?_)
  rw [show ((0 : ℝ) : UnitAddCircle) = (0 : UnitAddCircle) from by
    simp [QuotientAddGroup.mk_zero]]
  rw [fourier_eval_zero, mul_one]
  rfl

/-- Product form: for Schwartz `g, h : 𝓢(ℝ, ℂ)`,

`(∑' m : ℤ, g m) · (∑' n : ℤ, h n) = (∑' p : ℤ, 𝓕g p) · (∑' q : ℤ, 𝓕h q)`.

This is the simplest case of 2-D Poisson summation, applicable when the
2-D function `f(x, y) = g(x) · h(y)` is separable. -/
theorem tsum_product_eq_tsum_fourier_product (g h : 𝓢(ℝ, ℂ)) :
    ((∑' m : ℤ, (g : ℝ → ℂ) m) * (∑' n : ℤ, (h : ℝ → ℂ) n) : ℂ) =
      (∑' p : ℤ, 𝓕 (g : ℝ → ℂ) p) * (∑' q : ℤ, 𝓕 (h : ℝ → ℂ) q) := by
  rw [tsum_eq_tsum_fourier_zero g, tsum_eq_tsum_fourier_zero h]

/-- **Schwartz functions are summable on ℤ.**  For any Schwartz `f : 𝓢(ℝ, ℂ)`,
the restriction to integers is summable.  Follows from the `|x|^(-2)` decay
of Schwartz functions on ℝ. -/
lemma summable_int (f : 𝓢(ℝ, ℂ)) :
    Summable fun n : ℤ => (f : ℝ → ℂ) n :=
  summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
    ((f.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)

/-- **Schwartz functions are absolutely summable on ℤ.**  Stronger form of
`SchwartzMap.summable_int`: the norm `‖f n‖` is also summable. -/
lemma summable_norm_int (f : 𝓢(ℝ, ℂ)) :
    Summable fun n : ℤ => ‖(f : ℝ → ℂ) n‖ :=
  summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
    (((f.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite).norm_left)

-- Aliases for the private helpers used internally.
private alias schwartz_summable_int := summable_int
private alias schwartz_summable_norm_int := summable_norm_int

-- Helper lemmas for the products of summable Schwartz functions
-- (used implicitly via `tsum_mul_tsum_of_summable_norm` in the proof above).

/-- **Separable 2-D Poisson summation** (full form): for Schwartz `g, h : 𝓢(ℝ, ℂ)`,
the sum over `ℤ × ℤ` of `g(m) · h(n)` equals the sum over `ℤ × ℤ` of
`𝓕g(p) · 𝓕h(q)`.

This is the 2-D Poisson summation formula in the separable case (i.e., for
functions on `ℝ × ℝ` of the form `(x, y) ↦ g(x) · h(y)`).  The general
non-separable case requires the multi-dimensional Fourier transform on
`ℝ × ℝ` and corresponding multi-D Poisson summation. -/
theorem tsum_prod_eq_tsum_fourier_prod (g h : 𝓢(ℝ, ℂ)) :
    (∑' z : ℤ × ℤ, (g : ℝ → ℂ) z.1 * (h : ℝ → ℂ) z.2 : ℂ) =
      ∑' z : ℤ × ℤ, 𝓕 (g : ℝ → ℂ) z.1 * 𝓕 (h : ℝ → ℂ) z.2 := by
  -- Norm-summability on ℤ for g, h, 𝓕g, 𝓕h
  have hg_norm := schwartz_summable_norm_int g
  have hh_norm := schwartz_summable_norm_int h
  have hFg_norm : Summable fun n : ℤ => ‖𝓕 (g : ℝ → ℂ) n‖ := by
    have := schwartz_summable_norm_int (fourierTransformCLM ℝ g)
    convert this using 1
  have hFh_norm : Summable fun n : ℤ => ‖𝓕 (h : ℝ → ℂ) n‖ := by
    have := schwartz_summable_norm_int (fourierTransformCLM ℝ h)
    convert this using 1
  rw [← tsum_mul_tsum_of_summable_norm hg_norm hh_norm,
    ← tsum_mul_tsum_of_summable_norm hFg_norm hFh_norm]
  exact tsum_product_eq_tsum_fourier_product g h

/-- **Separable 3-D Poisson summation** (product form): for Schwartz functions
`g, h, k : 𝓢(ℝ, ℂ)`,

`(∑' m, g m) · (∑' n, h n) · (∑' p, k p) =
  (∑' m, 𝓕g m) · (∑' n, 𝓕h n) · (∑' p, 𝓕k p)`. -/
theorem tsum_three_product_eq_fourier (g h k : 𝓢(ℝ, ℂ)) :
    ((∑' m : ℤ, (g : ℝ → ℂ) m) * (∑' n : ℤ, (h : ℝ → ℂ) n) *
        (∑' p : ℤ, (k : ℝ → ℂ) p) : ℂ) =
      (∑' m : ℤ, 𝓕 (g : ℝ → ℂ) m) * (∑' n : ℤ, 𝓕 (h : ℝ → ℂ) n) *
        (∑' p : ℤ, 𝓕 (k : ℝ → ℂ) p) := by
  rw [tsum_eq_tsum_fourier_zero g, tsum_eq_tsum_fourier_zero h,
    tsum_eq_tsum_fourier_zero k]

/-- **Separable n-D Poisson summation** (product form): for a finite family of
Schwartz functions `f : ι → 𝓢(ℝ, ℂ)`,

`∏ i, (∑' m : ℤ, f i m) = ∏ i, (∑' m : ℤ, 𝓕(f i) m)`.

This is the general "tensor" version of the separable n-D Poisson summation,
following directly from the 1-D case applied factor-wise. -/
theorem tsum_finset_product_eq_fourier_product
    {ι : Type*} [Fintype ι] (f : ι → 𝓢(ℝ, ℂ)) :
    (∏ i, ∑' m : ℤ, ((f i : 𝓢(ℝ, ℂ)) : ℝ → ℂ) m) =
      ∏ i, ∑' m : ℤ, 𝓕 ((f i : 𝓢(ℝ, ℂ)) : ℝ → ℂ) m := by
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact tsum_eq_tsum_fourier_zero (f i)

/-- For empty index types, the empty Schwartz family trivially satisfies
Poisson summation: both sides equal 1.  Base case for the inductive
sum-over-product version. -/
theorem tsum_empty_product_eq_fourier_product
    {ι : Type*} [Fintype ι] [IsEmpty ι] (f : ι → 𝓢(ℝ, ℂ)) :
    (∑' z : ι → ℤ, ∏ i, ((f i : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (z i) : ℂ) =
      ∑' z : ι → ℤ, ∏ i, 𝓕 ((f i : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (z i) := by
  simp only [Finset.univ_eq_empty, Finset.prod_empty]

-- The full n-D sum-over-product version (a generalization of
-- `tsum_prod_eq_tsum_fourier_prod` to Fin n) is left as future work.  It
-- follows by induction on n, applying the 2-D version + Fubini for
-- tsum on Fin n → ℤ.  Each step requires careful summability arguments
-- via `tsum_mul_tsum_of_summable_norm`.

/-- Variant: 1-D Schwartz Poisson summation at half-integer shift.
For Schwartz `f : 𝓢(ℝ, ℂ)`,
`∑' n : ℤ, f (1/2 + n) = ∑' n : ℤ, 𝓕f n · (-1)^n`. -/
theorem tsum_eq_tsum_fourier_half (f : 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, (f : ℝ → ℂ) (1/2 + n)) =
      ∑' n : ℤ, 𝓕 (f : ℝ → ℂ) n * fourier n ((1/2 : ℝ) : UnitAddCircle) := by
  exact SchwartzMap.tsum_eq_tsum_fourier f (1/2)

/-- 2-D Schwartz Poisson at half-integer shift in one variable, separable case.
For `g, h : 𝓢(ℝ, ℂ)`,
`(∑' m, g(1/2 + m)) · (∑' n, h n) = ∑' (m, n), (𝓕g m · (-1)^m) · 𝓕h n`. -/
theorem tsum_half_product_eq_fourier (g h : 𝓢(ℝ, ℂ)) :
    ((∑' m : ℤ, (g : ℝ → ℂ) (1/2 + m)) * (∑' n : ℤ, (h : ℝ → ℂ) n) : ℂ) =
      (∑' m : ℤ, 𝓕 (g : ℝ → ℂ) m * fourier m ((1/2 : ℝ) : UnitAddCircle)) *
        (∑' n : ℤ, 𝓕 (h : ℝ → ℂ) n) := by
  rw [tsum_eq_tsum_fourier_half g, tsum_eq_tsum_fourier_zero h]

/-- 2-D Schwartz Poisson at arbitrary real shifts in both variables, separable case.
For `g, h : 𝓢(ℝ, ℂ)` and `a, b : ℝ`,
`(∑' m, g(a + m)) · (∑' n, h(b + n))`
`= (∑' m, 𝓕g m · fourier m a) · (∑' n, 𝓕h n · fourier n b)`. -/
theorem tsum_shift_product_eq_fourier (g h : 𝓢(ℝ, ℂ)) (a b : ℝ) :
    ((∑' m : ℤ, (g : ℝ → ℂ) (a + m)) * (∑' n : ℤ, (h : ℝ → ℂ) (b + n)) : ℂ) =
      (∑' m : ℤ, 𝓕 (g : ℝ → ℂ) m * fourier m ((a : ℝ) : UnitAddCircle)) *
        (∑' n : ℤ, 𝓕 (h : ℝ → ℂ) n * fourier n ((b : ℝ) : UnitAddCircle)) := by
  rw [SchwartzMap.tsum_eq_tsum_fourier g a, SchwartzMap.tsum_eq_tsum_fourier h b]
  rfl

end SchwartzMap
