import Mathlib

/-!
# Mathlib4 candidates: `FractionalIdeal.ringEquivOfRingEquiv` on coefficient ideals

Generic identity relating `FractionalIdeal.ringEquivOfRingEquiv` (transport
of fractional ideals along a `RingEquiv` of the base ring) to `Ideal.map`
on the underlying ideal.  Stated here for number fields; the proof is
purely generic over an `IsFractionRing` setup.

## Main result

* `ringEquivOfRingEquiv_coeIdeal` — `FractionalIdeal.ringEquivOfRingEquiv K K c
  (I : FractionalIdeal 𝓞⁰ K) = Ideal.map c I` (as fractional ideals).
-/

namespace Mathlib4_Extra

open NumberField FractionalIdeal
open scoped nonZeroDivisors

noncomputable section

/-- `FractionalIdeal.ringEquivOfRingEquiv` applied to a coefficient ideal equals
the image-ideal coerced.  Stated for number fields here but the proof is
purely generic over an `IsFractionRing` setup. -/
lemma ringEquivOfRingEquiv_coeIdeal (K : Type*) [Field K] [NumberField K]
    (c : (NumberField.RingOfIntegers K) ≃+* (NumberField.RingOfIntegers K))
    (I : Ideal (NumberField.RingOfIntegers K)) :
    FractionalIdeal.ringEquivOfRingEquiv K K c
        (I : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) =
    (Ideal.map (c : (NumberField.RingOfIntegers K) →+* (NumberField.RingOfIntegers K)) I :
      FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) := by
  ext x
  simp only [FractionalIdeal.ringEquivOfRingEquiv_apply, FractionalIdeal.val_eq_coe,
    FractionalIdeal.coe_coeIdeal, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, hy⟩
    refine ⟨c z, Ideal.mem_map_of_mem
      (c : (NumberField.RingOfIntegers K) →+* (NumberField.RingOfIntegers K)) hz, ?_⟩
    simpa [IsFractionRing.semilinearEquivOfRingEquiv_apply] using hy
  · rintro ⟨y, hy, rfl⟩
    have h_surj : Function.Surjective
        (c : (NumberField.RingOfIntegers K) →+* (NumberField.RingOfIntegers K)) := by
      intro x; refine ⟨c.symm x, ?_⟩; simp
    rcases (Ideal.mem_map_iff_of_surjective
        (c : (NumberField.RingOfIntegers K) →+* (NumberField.RingOfIntegers K)) h_surj).mp hy with
      ⟨z, hz, rfl⟩
    refine ⟨algebraMap (NumberField.RingOfIntegers K) K z, ⟨z, hz, rfl⟩, ?_⟩
    simp [IsFractionRing.semilinearEquivOfRingEquiv_apply]

end

end Mathlib4_Extra
