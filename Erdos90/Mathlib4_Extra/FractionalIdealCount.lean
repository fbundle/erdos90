import Mathlib

/-!
# Mathlib4 candidates: lemmas about `FractionalIdeal`

Generic lemmas about `FractionalIdeal` in a Dedekind domain / number-field
context, intended for upstreaming to Mathlib4.  Currently used by
`Erdos90.CMField.QScaling` and `Erdos90.CMField.Basic`.

## Main results

* `le_one_of_forall_count_nonneg` — a nonzero fractional ideal with
  everywhere-nonneg count is bounded by 1 (hence integral).
* `mem_range_of_spanSingleton_count_nonneg` — for `y : K` nonzero with
  `count K v (spanSingleton y) ≥ 0` at every height-one prime `v`, the
  element `y` lies in the image of `algebraMap R K`.
* `ringEquivOfRingEquiv_coeIdeal` — `FractionalIdeal.ringEquivOfRingEquiv`
  applied to a coefficient ideal equals the image-ideal coerced.
-/

namespace Mathlib4_Extra

open NumberField FractionalIdeal IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- A nonzero fractional ideal `I` of a Dedekind domain is bounded by `1` iff
all of its `count`s are nonnegative.  This file proves the easier "←" direction;
the converse follows from `count_mono` + `count_coe_nonneg`. -/
theorem le_one_of_forall_count_nonneg {I : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, 0 ≤ FractionalIdeal.count K v I) :
    I ≤ 1 := by
  -- Use the factorization theorem `finprod_heightOneSpectrum_factorization'`.
  -- All exponents nonneg ⟹ I is a product of integer-ideal-powers ⟹ I ≤ 1.
  have hfac := FractionalIdeal.finprod_heightOneSpectrum_factorization' (R := R) (K := K) hI
  -- Rewrite each factor with ℕ exponent via finprod_congr
  have hfac' : ∏ᶠ v : HeightOneSpectrum R,
      (v.asIdeal : FractionalIdeal R⁰ K) ^ ((FractionalIdeal.count K v I).toNat) = I := by
    calc ∏ᶠ v : HeightOneSpectrum R,
          (v.asIdeal : FractionalIdeal R⁰ K) ^ ((FractionalIdeal.count K v I).toNat)
        = ∏ᶠ v : HeightOneSpectrum R,
            (v.asIdeal : FractionalIdeal R⁰ K) ^ (FractionalIdeal.count K v I) := by
          refine finprod_congr (fun v => ?_)
          rw [← zpow_natCast (v.asIdeal : FractionalIdeal R⁰ K)
                ((FractionalIdeal.count K v I).toNat)]
          congr 1
          exact Int.toNat_of_nonneg (h v)
      _ = I := hfac
  rw [← hfac']
  -- finprod is a finite product; bound each factor by 1.
  have hmulSupport_finite :
      (Function.mulSupport (fun v : HeightOneSpectrum R =>
        (v.asIdeal : FractionalIdeal R⁰ K) ^ ((FractionalIdeal.count K v I).toNat))).Finite := by
    have hfin_count : Set.Finite {v : HeightOneSpectrum R |
        FractionalIdeal.count K v I ≠ 0} :=
      Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)
    apply hfin_count.subset
    intro v hv
    by_contra hcount0
    apply hv
    show ((v.asIdeal : FractionalIdeal R⁰ K) ^ ((FractionalIdeal.count K v I).toNat)) = 1
    have h_count_zero : (FractionalIdeal.count K v I).toNat = 0 := by
      rw [Int.toNat_eq_zero]
      by_contra hne
      apply hcount0
      have hpos : 0 < FractionalIdeal.count K v I := lt_of_not_ge hne
      exact hpos.ne'
    rw [h_count_zero]; simp
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hmulSupport_finite.toFinset)
    (by intro x hx; exact hmulSupport_finite.mem_toFinset.mpr hx)]
  -- Now we have a finite product over hmulSupport_finite.toFinset.
  -- Each factor (v.asIdeal)^n is ≤ 1 since v.asIdeal ≤ 1 (it's a coerced ideal).
  apply Finset.prod_le_one
  · intro v _
    positivity
  · intro v _
    apply pow_le_one₀
    · exact zero_le _
    · exact FractionalIdeal.coeIdeal_le_one

/-- For `y : K` nonzero, `y` lies in `(algebraMap R K).range` iff all `count`s
of `spanSingleton R⁰ y` are nonneg. -/
theorem mem_range_of_spanSingleton_count_nonneg {y : K} (hy : y ≠ 0)
    (h : ∀ v : HeightOneSpectrum R,
      0 ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ y)) :
    y ∈ (algebraMap R K).range := by
  have hy_span_ne : (FractionalIdeal.spanSingleton R⁰ y) ≠ 0 := by
    intro h_span
    rw [FractionalIdeal.spanSingleton_eq_zero_iff] at h_span
    exact hy h_span
  have h_le : FractionalIdeal.spanSingleton R⁰ y ≤ 1 :=
    le_one_of_forall_count_nonneg (R := R) (K := K) hy_span_ne h
  rw [FractionalIdeal.spanSingleton_le_iff_mem] at h_le
  rcases (FractionalIdeal.mem_one_iff R⁰).mp h_le with ⟨a, ha⟩
  exact ⟨a, ha⟩

end

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

end Mathlib4_Extra
