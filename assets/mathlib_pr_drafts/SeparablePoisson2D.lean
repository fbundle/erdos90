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

/-- Summability on ℤ for Schwartz functions, via `|x|^(-2)` decay. -/
private lemma schwartz_summable_int (f : 𝓢(ℝ, ℂ)) :
    Summable fun n : ℤ => (f : ℝ → ℂ) n :=
  summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
    ((f.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)

/-- Norm-summability on ℤ for Schwartz functions. -/
private lemma schwartz_summable_norm_int (f : 𝓢(ℝ, ℂ)) :
    Summable fun n : ℤ => ‖(f : ℝ → ℂ) n‖ :=
  summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
    (((f.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite).norm_left)

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

end SchwartzMap
