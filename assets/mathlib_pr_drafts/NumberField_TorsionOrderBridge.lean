/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
-- This file also implicitly depends on the "reverse totient inequality"
-- (see Nat_TotientReverse.lean draft) but we state without it for now.

/-!
# Bridge from `torsionOrder` to field degree via the cyclotomic structure

For a number field K, the torsion subgroup of `(𝓞 K)ˣ` is a finite cyclic
group of order `torsionOrder K`.  Its generator is a primitive
`torsionOrder K`-th root of unity in K.  By cyclotomic theory,
`[ℚ(ζ_n) : ℚ] = φ(n)`, and `ℚ(ζ_{torsionOrder K}) ⊆ K`, hence:

```
(torsionOrder K).totient ≤ Module.finrank ℚ K
```

This is a Mathlib PR candidate extracted from the Erd46 formalization.

## Main results

* `NumberField.Units.totient_torsionOrder_le_finrank`: the bridge inequality.

The proof follows the pattern from
`Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.lean`
`IsCyclotomicExtension.Rat.torsionOrder_eq`: extract a primitive root from
the cyclic torsion subgroup, lift to K, apply
`IsPrimitiveRoot.lcm_totient_le_finrank` with `Nat.lcm_self`.
-/

namespace NumberField.Units

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in
/-- For a number field K, the totient of the torsion order is at most the
field's degree over ℚ. -/
lemma totient_torsionOrder_le_finrank :
    (NumberField.Units.torsionOrder K).totient ≤ Module.finrank ℚ K := by
  set n := NumberField.Units.torsionOrder K with hn_def
  have hn_pos : 0 < n := NumberField.Units.torsionOrder_pos K
  obtain ⟨μ, hμ⟩ : ∃ μ : NumberField.Units.torsion K, orderOf μ = n := by
    rw [hn_def, NumberField.Units.torsionOrder, Fintype.card_eq_nat_card]
    exact IsCyclic.exists_ofOrder_eq_natCard
  rw [← IsPrimitiveRoot.iff_orderOf, ← IsPrimitiveRoot.coe_submonoidClass_iff,
    ← IsPrimitiveRoot.coe_units_iff] at hμ
  replace hμ := hμ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have hirr : Irreducible (Polynomial.cyclotomic n ℚ) :=
    Polynomial.cyclotomic.irreducible_rat hn_pos
  have h := IsPrimitiveRoot.lcm_totient_le_finrank hμ hμ
    (by rw [Nat.lcm_self]; exact hirr)
  rwa [Nat.lcm_self] at h

end NumberField.Units
