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

/-- **Separable 2-D Poisson summation**: for Schwartz `g, h : 𝓢(ℝ, ℂ)`,

`(∑' m : ℤ, g m) · (∑' n : ℤ, h n) = (∑' p : ℤ, 𝓕g p) · (∑' q : ℤ, 𝓕h q)`.

This is the simplest case of 2-D Poisson summation, applicable when the
2-D function `f(x, y) = g(x) · h(y)` is separable. -/
theorem tsum_product_eq_tsum_fourier_product (g h : 𝓢(ℝ, ℂ)) :
    ((∑' m : ℤ, (g : ℝ → ℂ) m) * (∑' n : ℤ, (h : ℝ → ℂ) n) : ℂ) =
      (∑' p : ℤ, 𝓕 (g : ℝ → ℂ) p) * (∑' q : ℤ, 𝓕 (h : ℝ → ℂ) q) := by
  rw [tsum_eq_tsum_fourier_zero g, tsum_eq_tsum_fourier_zero h]

end SchwartzMap
