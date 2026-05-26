import Mathlib
import Erdos90.NumberFieldDeep

/-!
# Counterexample: `classNumBound_nonpos` is false for the GS tower (HISTORICAL)

**Status**: HISTORICAL — the architectural issue this file documents has
already been resolved by the 2026-05-25 refactor.  `CMTowerData` no longer
has a `classNumBound_nonpos` field; instead `cm_norm_one_elements` takes
`classNumBound_le_log_H : cmData.classNumBound ≤ log_H` as an explicit
hypothesis, which is supplied by `brd_cm_tower_postulate` from `brd_tower_data`.

This file remains as documentation of the past architectural decision and
why the previous design was rejected.

## The historical issue

In an earlier version of `CMTowerData`, the field `classNumBound_nonpos`
asserted `classNumBound ≤ 0`.  Given the tower's

    classNumBound := Real.log (h_K : ℝ) / (f : ℝ)

`classNumBound_nonpos` would mean `log(h_K)/f ≤ 0`, i.e. `h_K = 1`.

The GS tower picks K = ℚ(ζ_p) for large primes p.  By Masley–Montgomery
(1976), `h_K > 1` for all p ≥ 23.  So `classNumBound_nonpos` was
mathematically FALSE.

## Resolution applied (2026-05-25)

Replaced `classNumBound_nonpos : classNumBound ≤ 0` with
`classNumBound_le_log_H : classNumBound ≤ log_H` — the Minkowski class-number
bound, which is mathematically TRUE.  See Phase D5 in CLAUDE.md for the
refactor history.

## What this file still proves

1. **Equivalence**: `classNumBound ≤ 0` (with the tautological definition)
   ↔ `classNumber K = 1`. (Fully proved, no sorries.)

2. **Masley–Montgomery gap (sorried)**: `∃ p prime, p > 5, classNumber(ℚ(ζ_p)) ≠ 1`.
   Documented as a counterexample but not closed (Masley–Montgomery is not
   in Mathlib v4.30).  Off the proof path of `erdos_unit_distance_false`.
-/

open NumberField

noncomputable section

/-! ### Equivalence: `classNumBound_nonpos` ↔ h_K = 1 -/

/-- `classNumBound_nonpos` (with the tautological definition `Real.log(h_K)/f`)
is equivalent to `h_K = 1`. -/
theorem classNumBound_nonpos_iff_classNumber_one
    {K : Type} [Field K] [NumberField K] (f : ℕ) (hf : f > 0) :
    ((Real.log ((Fintype.card (ClassGroup (𝓞 K)) : ℝ)) / (f : ℝ)) ≤ 0) ↔
    (Fintype.card (ClassGroup (𝓞 K)) : ℕ) = 1 := by
  have hcard_pos_ℕ : 0 < Fintype.card (ClassGroup (𝓞 K)) :=
    Fintype.card_pos (α := ClassGroup (𝓞 K))
  have hcard_ge_one_ℕ : 1 ≤ Fintype.card (ClassGroup (𝓞 K)) :=
    Nat.one_le_of_lt hcard_pos_ℕ
  have hcard_pos_ℝ : (0 : ℝ) < (Fintype.card (ClassGroup (𝓞 K)) : ℝ) := by
    exact_mod_cast hcard_pos_ℕ
  have hf_pos : (0 : ℝ) < (f : ℝ) := Nat.cast_pos.mpr hf
  have hlog_nn : 0 ≤ Real.log ((Fintype.card (ClassGroup (𝓞 K)) : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast hcard_ge_one_ℕ)
  constructor
  · intro h
    have hlog_le0 : Real.log ((Fintype.card (ClassGroup (𝓞 K)) : ℝ)) ≤ 0 := by
      have h_div_cases := (div_nonpos_iff (a := Real.log ((Fintype.card (ClassGroup (𝓞 K)) : ℝ)))
        (b := (f : ℝ))).mp h
      rcases h_div_cases with (⟨hpos, hneg⟩ | ⟨hle, hnonneg⟩)
      · linarith [hf_pos, hneg]
      · exact hle
    have hlog_eq0 : Real.log ((Fintype.card (ClassGroup (𝓞 K)) : ℝ)) = 0 := by
      linarith
    have hcard1_ℝ : (Fintype.card (ClassGroup (𝓞 K)) : ℝ) = 1 := by
      calc
        (Fintype.card (ClassGroup (𝓞 K)) : ℝ) = Real.exp (Real.log ((Fintype.card (ClassGroup (𝓞 K)) : ℝ))) := by
          rw [Real.exp_log hcard_pos_ℝ]
        _ = Real.exp 0 := by rw [hlog_eq0]
        _ = 1 := Real.exp_zero
    -- Use Nat.cast_inj to go from ℝ equality to ℕ equality
    apply (Nat.cast_inj (R := ℝ)).mp
    calc
      ((Fintype.card (ClassGroup (𝓞 K)) : ℕ) : ℝ) = (Fintype.card (ClassGroup (𝓞 K)) : ℝ) := by simp
      _ = 1 := hcard1_ℝ
      _ = ((1 : ℕ) : ℝ) := by simp
  · intro h
    have hcard1_ℝ : (Fintype.card (ClassGroup (𝓞 K)) : ℝ) = 1 := by exact_mod_cast h
    have hzero : Real.log ((Fintype.card (ClassGroup (𝓞 K)) : ℝ)) / (f : ℝ) = 0 := by
      rw [hcard1_ℝ, Real.log_one, zero_div]
    rw [hzero]

/-! ### The Minkowski criterion fails for p ≥ 7

`isPrincipalIdealRing_of_abs_discr_lt` is the only PID-proving tool in Mathlib
for cyclotomic fields.  It requires |disc(K)| < Minkowski_bound(finrank, nrComplexPlaces).

For ℚ(ζ_p): finrank = p-1, nrComplexPlaces = (p-1)/2, |disc| = p^{p-2}.
The inequality p^{p-2} < (…)^2 fails for p ≥ 7.
-/

lemma minkowski_pid_criterion_fails_for_cyclotomic_p_ge_7 (p : ℕ) [Fact (Nat.Prime p)] (hp : 7 ≤ p)
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    let finrank_ℚ := Module.finrank ℚ K
    let nrComplex := InfinitePlace.nrComplexPlaces K
    |discr K| ≥ (2 * ((π : ℝ) / 4) ^ nrComplex *
      (((finrank_ℚ : ℝ) ^ finrank_ℚ) / ((Nat.factorial finrank_ℚ : ℝ)))) ^ 2 := by
  intro finrank_ℚ nrComplex
  -- GAP: requires bounding p^{p-2} from below by the Minkowski RHS
  sorry

/-! ### The Masley–Montgomery gap

The class number 1 problem for cyclotomic fields was settled by Masley and
Montgomery (1976): ℚ(ζ_p) has class number 1 iff p ≤ 19.

For the GS tower, p is large (p ≥ 2M+1 where M is the tower level count),
so h_K > 1.  This makes `classNumBound_nonpos` mathematically false. -/

/-- There exists a prime p > 5 such that ℚ(ζ_p) does NOT have class number 1.
The smallest such p is 23 (h = 3).  Proof: Masley–Montgomery (1976). -/
def exists_cyclotomic_not_PID : ∃ (p : ℕ), Nat.Prime p ∧ 5 < p ∧
    ¬ IsPrincipalIdealRing (𝓞 (CyclotomicField p ℚ)) := by
  -- GAP: requires Masley–Montgomery or explicit ideal construction
  sorry

/-- Consequence: there exists a cyclotomic field with class number ≠ 1. -/
def exists_cyclotomic_classNumber_ne_one : ∃ (p : ℕ), Nat.Prime p ∧ 5 < p ∧
    (Fintype.card (ClassGroup (𝓞 (CyclotomicField p ℚ))) : ℕ) ≠ 1 := by
  obtain ⟨p, hp, hp_gt, h_not_pid⟩ := exists_cyclotomic_not_PID
  refine ⟨p, hp, hp_gt, ?_⟩
  intro hcard
  apply h_not_pid
  have hclassNumber : NumberField.classNumber (CyclotomicField p ℚ) = 1 := by
    rw [NumberField.classNumber, hcard]
  exact ((NumberField.classNumber_eq_one_iff (K := CyclotomicField p ℚ)).mp hclassNumber)

/-- For any p > 5 such that ℚ(ζ_p) has class number ≠ 1,
`classNumBound_nonpos` (with tautological `classNumBound`) is false. -/
theorem classNumBound_nonpos_false_of_classNumber_ne_one
    (p : ℕ) (hp : 5 < p)
    (hcard_ne_one : (Fintype.card (ClassGroup (𝓞 (CyclotomicField p ℚ))) : ℕ) ≠ 1) :
    ¬ (Real.log ((Fintype.card (ClassGroup (𝓞 (CyclotomicField p ℚ))) : ℝ)) /
      (((p - 1) / 2 : ℕ) : ℝ) ≤ 0) := by
  intro h_nonpos
  have hf_pos : 0 < (p - 1) / 2 := by
    have hp_gt_1 : 1 < p := by omega
    have h_sub_pos : 0 < p - 1 := by omega
    omega
  have hcard1 := ((classNumBound_nonpos_iff_classNumber_one
    (f := (p - 1) / 2) (hf := hf_pos) (K := CyclotomicField p ℚ)).mp h_nonpos)
  exact hcard_ne_one hcard1

end
