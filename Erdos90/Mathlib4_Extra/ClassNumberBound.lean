import Mathlib

/-!
# Mathlib4 candidates: class number bounds via the Minkowski bound

Crude upper bounds on `Fintype.card (ClassGroup (𝓞 K))` via the Minkowski
bound `NumberField.minkBound K` and the count of bounded-norm ideals.

The eventual goal is to bound `log h_K / nrComplexPlaces K` by a function of
the root discriminant `rd_F`, en route to closing the Brauer–Siegel sorry
in `Erdos90/NumberFieldDeep_GSTower.lean` (Phase E).

## Main results

* `Mathlib4_Extra.classNumber_le_card_ideals_of_norm_le_minkowski` — the
  class number is bounded by the count of ideals of `𝓞 K` with absolute
  norm at most `⌊minkBound K⌋₊`.  Proved using `exists_ideal_in_class_of_norm_le`
  + an injection from `ClassGroup` to `{ideal | absNorm ≤ ⌊minkBound K⌋₊}`.

* `Mathlib4_Extra.card_ideals_of_norm_le_bound` — for a number field of
  degree `n` and bound `N`, the number of ideals of `𝓞 K` with absolute
  norm at most `N` is bounded by `N ^ n`.  Sorried; this is the Mathlib
  gap (a crude polynomial bound that follows from the divisor-function
  estimate but isn't packaged in Mathlib v4.30).
-/

namespace Mathlib4_Extra

open NumberField Ideal
open scoped NumberField nonZeroDivisors Real

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

-- Mirror the Minkowski bound from `Mathlib.NumberTheory.NumberField.ClassNumber`
-- (where it's only available as a local notation).
private noncomputable abbrev minkBound : ℝ :=
  (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
    ((Nat.factorial (Module.finrank ℚ K) : ℝ) /
      (Module.finrank ℚ K : ℝ) ^ (Module.finrank ℚ K) *
      Real.sqrt |NumberField.discr K|)

/-- The class number is bounded by the number of ideals of `𝓞 K` of absolute
norm at most `⌊minkBound K⌋₊` (the floor of the Minkowski bound).

This is a direct consequence of `NumberField.exists_ideal_in_class_of_norm_le`:
each class has a representative ideal with norm ≤ minkBound K, and the assignment
class ↦ rep is injective (its left inverse is `ClassGroup.mk0`). -/
theorem classNumber_le_card_ideals_of_norm_le_minkowski :
    Fintype.card (ClassGroup (𝓞 K)) ≤
      Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ ⌊minkBound K⌋₊} := by
  -- Build the injection ClassGroup K → {ideals with norm ≤ ⌊minkBound K⌋₊}
  classical
  -- For each class C, pick a representative ideal with norm ≤ minkBound K
  have h_exists (C : ClassGroup (𝓞 K)) :
      ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = C ∧
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ minkBound K := by
    obtain ⟨I, hI_mk, hI_norm⟩ := exists_ideal_in_class_of_norm_le C
    exact ⟨I, hI_mk, hI_norm⟩
  -- Define the choice function
  let f : ClassGroup (𝓞 K) → {I : (Ideal (𝓞 K))⁰ //
      Ideal.absNorm (I : Ideal (𝓞 K)) ≤ ⌊minkBound K⌋₊} := fun C =>
    let I := Classical.choose (h_exists C)
    let h := Classical.choose_spec (h_exists C)
    ⟨I, Nat.le_floor h.2⟩
  -- f is injective: if f C = f C' then ClassGroup.mk0 (f C) = ClassGroup.mk0 (f C'), so C = C'
  have hf_inj : Function.Injective f := by
    intro C C' h_eq
    have h_I_eq : (f C).val = (f C').val := congrArg Subtype.val h_eq
    have h_mk_C : ClassGroup.mk0 (Classical.choose (h_exists C)) = C :=
      (Classical.choose_spec (h_exists C)).1
    have h_mk_C' : ClassGroup.mk0 (Classical.choose (h_exists C')) = C' :=
      (Classical.choose_spec (h_exists C')).1
    simp only [f] at h_I_eq
    rw [← h_mk_C, ← h_mk_C', h_I_eq]
  -- Conclude: |ClassGroup K| ≤ |{ideals with norm ≤ ⌊minkBound K⌋₊}|
  have h_card_le : Fintype.card (ClassGroup (𝓞 K)) ≤
      Nat.card {I : (Ideal (𝓞 K))⁰ //
        Ideal.absNorm (I : Ideal (𝓞 K)) ≤ ⌊minkBound K⌋₊} := by
    haveI : Finite {I : (Ideal (𝓞 K))⁰ //
        Ideal.absNorm (I : Ideal (𝓞 K)) ≤ ⌊minkBound K⌋₊} := by
      have h := Ideal.finite_setOf_absNorm_le₀ (S := 𝓞 K) (⌊minkBound K⌋₊)
      exact h.to_subtype
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective f hf_inj
  exact h_card_le

/-- **Mathlib gap (Phase E1 sorry):** For a number field `K` of degree `n` and
a positive integer bound `N`, the number of nonzero ideals of `𝓞 K` with
absolute norm at most `N` is bounded by `N ^ n`.

This is a crude polynomial bound, looser than the standard analytic estimate
`O(N · polylog N)`.  It follows from the divisor-function bound
`|{ideals of norm = m}| ≤ d(m)^n ≤ m^n`, but is not packaged in Mathlib
v4.30.  TRUE; a clean Mathlib-PR-shaped statement. -/
theorem card_ideals_of_norm_le_bound (N : ℕ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N} ≤
      N ^ (Module.finrank ℚ K) := sorry

/-- Combined: `Fintype.card (ClassGroup (𝓞 K)) ≤ ⌊minkBound K⌋₊ ^ [K:ℚ]`. -/
theorem classNumber_le_minkowski_pow_degree :
    Fintype.card (ClassGroup (𝓞 K)) ≤ ⌊minkBound K⌋₊ ^ (Module.finrank ℚ K) :=
  (classNumber_le_card_ideals_of_norm_le_minkowski K).trans
    (card_ideals_of_norm_le_bound K ⌊minkBound K⌋₊)

end

end Mathlib4_Extra
