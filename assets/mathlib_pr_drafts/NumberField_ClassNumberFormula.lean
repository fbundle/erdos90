/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Class number formula as an algebraic identity

Mathlib's `NumberField.dedekindZeta_residue_def` gives the residue of `ζ_K` at
`s = 1` as a closed-form expression involving `classNumber K`, the regulator,
the discriminant, and the torsion order:
```
dedekindZeta_residue K = (2^r₁ · (2π)^r₂ · regulator K · classNumber K) /
                          (torsionOrder K · √|discr K|)
```

This file provides the same identity solved for `classNumber K`, which is the
form often needed in applications:
```
classNumber K = dedekindZeta_residue K · torsionOrder K · √|discr K| /
                  (2^r₁ · (2π)^r₂ · regulator K)
```

This is purely an algebraic rearrangement.  No analytic content (the analytic
content is in `tendsto_sub_one_mul_dedekindZeta_nhdsGT`).

This is a Mathlib PR candidate extracted from the Erd46 formalization.
-/

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

open Real

/-- The Dirichlet class number formula in algebraic-identity form.  Solving
`dedekindZeta_residue K = ...` for `classNumber K`. -/
lemma classNumber_eq_residue_formula :
    (NumberField.classNumber K : ℝ) =
      NumberField.dedekindZeta_residue K *
        (NumberField.Units.torsionOrder K * Real.sqrt |(NumberField.discr K : ℝ)|) /
      (2 ^ NumberField.InfinitePlace.nrRealPlaces K *
        (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
        NumberField.Units.regulator K) := by
  have h_reg_pos : 0 < NumberField.Units.regulator K := NumberField.Units.regulator_pos K
  have h_tors_pos : 0 < (NumberField.Units.torsionOrder K : ℝ) :=
    Nat.cast_pos.mpr (NumberField.Units.torsionOrder_pos K)
  have h_disc_ne : (NumberField.discr K : ℝ) ≠ 0 :=
    Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K)
  have h_sqrt_pos : 0 < Real.sqrt |(NumberField.discr K : ℝ)| :=
    Real.sqrt_pos_of_pos (abs_pos.mpr h_disc_ne)
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_two_pi_pos : 0 < 2 * Real.pi := by positivity
  have h_denom_ne : (2 : ℝ) ^ NumberField.InfinitePlace.nrRealPlaces K *
      (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
      NumberField.Units.regulator K ≠ 0 := by positivity
  have h_factor_ne : (NumberField.Units.torsionOrder K : ℝ) *
      Real.sqrt |(NumberField.discr K : ℝ)| ≠ 0 := by positivity
  rw [NumberField.dedekindZeta_residue_def]
  field_simp

end NumberField
