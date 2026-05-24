import Mathlib
import Erdos90.CMField.Basic

open Set Polynomial NumberField Ideal
open scoped BigOperators Complex

noncomputable section

/-!
# Split primes in cyclotomic CM fields

For K = ℚ(ζ_p) (p an odd prime), we construct `SplitPrimeData` using rational
primes q ≡ 1 (mod p).  Each such q splits completely in K, giving f = (p-1)/2
conjugate pairs of prime ideals.

## Main definitions

* `splitPrimeData_of_cyclotomic` — For K = ℚ(ζ_p), given t (number of rational primes),
  constructs `SplitPrimeData K (t * ((p-1)/2))`.  Requires 2 < p (odd prime > 2).

## Implementation status

- `find_t_primes_modEq_one`: fully proved (Dirichlet-based prime finding).
- Factorization lemmas (`inertiaDeg_eq_one`, `ramificationIdx_eq_one`,
  `card_primesOver_eq`, `conjIdeal_ne_self`): sorried, require the
  `Mathlib/NumberTheory/RamificationInertia` API.
- `splitPrimeData_from_prime_list`: sorried, depends on factorization lemmas.
- `splitPrimeData_of_cyclotomic`: sorried, depends on `splitPrimeData_from_prime_list`.
-/

namespace Erdos90.CMField.Cyclotomic

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp_gt_two : Fact (2 < p)]

/-- The cyclotomic CM field ℚ(ζ_p). -/
abbrev CycloK : Type _ := CyclotomicField p ℚ

/-- f = (p-1)/2 = nrComplexPlaces. -/
abbrev cyclof : ℕ := (p - 1) / 2

local notation "K" => CycloK p

section instances

variable {p}

instance : Field K := inferInstance
instance : NumberField K := inferInstance

instance : NeZero (p : ℚ) := NeZero.of_pos (Nat.cast_pos.mpr (Nat.Prime.pos hp.1))

instance : IsCyclotomicExtension {p} ℚ K :=
  CyclotomicField.isCyclotomicExtension (p) (ℚ)

instance : IsCMField K :=
  IsCyclotomicExtension.Rat.isCMField K (S := {p}) ⟨p, by simp, hp_gt_two.out⟩

instance : IsGalois ℚ K := IsCyclotomicExtension.isGalois {p} ℚ K

omit hp in lemma cyclof_pos : 0 < cyclof p := by
  dsimp [cyclof]
  have hp_gt_2 : 2 < p := hp_gt_two.out
  have h_sub_ge_2 : 2 ≤ p - 1 := by omega
  have hdiv := Nat.div_pos h_sub_ge_2 (by omega)
  omega

omit hp in lemma cyclof_ge_one : 1 ≤ cyclof p := Nat.one_le_of_lt cyclof_pos

end instances

/-!
## Dirichlet-based prime finding (fully proved)
-/

/-- Use Dirichlet's theorem to find t distinct primes q₁, ..., q_t ≡ 1 (mod p),
each ≠ p.  Uses `Nat.exists_prime_gt_modEq_one`. -/
def find_t_primes_modEq_one (t : ℕ) : ∃ qs : List ℕ,
    qs.length = t ∧
    (∀ q ∈ qs, Nat.Prime q) ∧
    (∀ q ∈ qs, q ≡ 1 [MOD p]) ∧
    (∀ q ∈ qs, q ≠ p) ∧
    qs.Nodup := by
  have hp_pos : p ≠ 0 := Nat.Prime.ne_zero hp.1
  induction' t with t ih
  · exact ⟨[], rfl, by simp, by simp, by simp, List.nodup_nil⟩
  · rcases ih with ⟨qs, h_len, h_prime, h_mod, h_ne_p, h_nodup⟩
    -- Compute the max of qs (or p if qs is empty, but qs has length t which may be 0)
    let M := qs.foldr max p
    have hM_bound : ∀ q' ∈ qs, q' ≤ M := by
      intro q' hq'
      dsimp [M]
      exact List.le_max_of_le' p hq' (le_refl q')
    rcases Nat.exists_prime_gt_modEq_one M hp_pos with ⟨q, hq_prime, hq_gt, hq_mod⟩
    have h_foldr_ge_base : ∀ (l : List ℕ) (b : ℕ), b ≤ l.foldr max b := by
      intro l b
      induction' l with a as ih
      · exact le_refl b
      · rw [List.foldr]
        exact le_trans ih (le_max_right _ _)
    have hM_ge_p : p ≤ M := by
      dsimp [M]; exact h_foldr_ge_base qs p
    have hq_ne_p : q ≠ p := by
      intro heq
      rw [heq] at hq_gt
      omega
    have hq_not_mem : q ∉ qs := by
      intro hq_mem
      have hq_le_M : q ≤ M := hM_bound q hq_mem
      omega
    have h_prime' : ∀ r ∈ q :: qs, Nat.Prime r := by
      intro r hr
      rcases List.mem_cons.mp hr with (h | h)
      · rw [h]; exact hq_prime
      · exact h_prime r h
    have h_mod' : ∀ r ∈ q :: qs, r ≡ 1 [MOD p] := by
      intro r hr
      rcases List.mem_cons.mp hr with (h | h)
      · rw [h]; exact hq_mod
      · exact h_mod r h
    have h_ne_p' : ∀ r ∈ q :: qs, r ≠ p := by
      intro r hr
      rcases List.mem_cons.mp hr with (h | h)
      · rw [h]; exact hq_ne_p
      · exact h_ne_p r h
    exact ⟨q :: qs, by simp [h_len], h_prime', h_mod', h_ne_p',
      List.nodup_cons.mpr ⟨hq_not_mem, h_nodup⟩⟩

/-!
## ANT lemmas (sorried, require Mathlib ramification/inertia API)
-/

section factorization_lemmas

variable (q : ℕ) [hq_prime : Fact (Nat.Prime q)]
variable (hq_mod : q ≡ 1 [MOD p]) (hq_ne_p : q ≠ p)

lemma inertiaDeg_eq_one (P : Ideal (𝓞 K)) [hP_prime : P.IsPrime]
    [hP_lies : P.LiesOver (span {(q : ℤ)})] :
    inertiaDeg (span {(q : ℤ)}) P = 1 := by
  sorry

lemma ramificationIdx_eq_one (P : Ideal (𝓞 K)) [hP_prime : P.IsPrime]
    [hP_lies : P.LiesOver (span {(q : ℤ)})] :
    ramificationIdx (span {(q : ℤ)}) P = 1 := by
  sorry

lemma card_primesOver_eq :
    Finset.card (IsDedekindDomain.primesOverFinset (Ideal.span {(q : ℤ)}) (𝓞 K)) = p - 1 := by
  sorry

lemma conjIdeal_ne_self (P : Ideal (𝓞 K)) [hP_prime : P.IsPrime]
    [hP_lies : P.LiesOver (Ideal.span {(q : ℤ)})] :
    conjIdeal K P ≠ P := by
  sorry

end factorization_lemmas

/-!
## Main construction (sorried, depends on factorization lemmas)
-/

/-- Given t distinct rational primes q₁,...,q_t ≡ 1 (mod p), select exactly one prime
from each conjugate pair for each qᵢ to obtain `SplitPrimeData K (t * cyclof p)`. -/
def splitPrimeData_from_prime_list (t : ℕ) (qs : List ℕ)
    (_hqs_prime : ∀ q ∈ qs, Nat.Prime q)
    (_hqs_mod : ∀ q ∈ qs, q ≡ 1 [MOD p])
    (_hqs_ne_p : ∀ q ∈ qs, q ≠ p)
    (_hqs_nodup : qs.Nodup) :
    SplitPrimeData K (t * cyclof p) := by
  sorry

/-- **Main construction**: For K = ℚ(ζ_p) with odd prime p > 2, and any t ∈ ℕ,
construct `SplitPrimeData K (t * ((p-1)/2))` using Dirichlet's theorem. -/
def splitPrimeData_of_cyclotomic (t : ℕ) : SplitPrimeData K (t * cyclof p) :=
  have h_nonempty : Nonempty (SplitPrimeData K (t * cyclof p)) := by
    have r := find_t_primes_modEq_one (p := p) t
    rcases r with ⟨qs, h_len, h_prime, h_mod, h_ne_p, h_nodup⟩
    exact ⟨splitPrimeData_from_prime_list (p := p) t qs h_prime h_mod h_ne_p h_nodup⟩
  h_nonempty.some

end Erdos90.CMField.Cyclotomic
