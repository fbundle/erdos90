import Mathlib
import Erdos90.CMField.Basic

open Real Set Polynomial NumberField Ideal DedekindDomain
open scoped BigOperators Complex

noncomputable section

/-!
# Split primes in cyclotomic CM fields

For K = ℚ(ζ_p) (p an odd prime), we construct `SplitPrimeData` using rational
primes q ≡ 1 (mod p).  Each such q splits completely in K, giving f = (p-1)/2
conjugate pairs of prime ideals.  Using Dirichlet's theorem, we obtain
arbitrarily many such q.

## Main definition

* `splitPrimeData_of_cyclotomic` — For K = ℚ(ζ_p), given t (number of rational primes),
  constructs `SplitPrimeData K (t * ((p-1)/2))`.  Requires 2 < p (odd prime > 2).
-/

namespace Erdos90.CMField.Cyclotomic

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (hp_gt_two : 2 < p)

/-- The cyclotomic CM field ℚ(ζ_p). -/
abbrev CycloK : Type _ := CyclotomicField p ℚ

/-- f = (p-1)/2 = nrComplexPlaces. -/
abbrev cyclof : ℕ := (p - 1) / 2

local notation "K" => CycloK p

section instances

variable {p}

instance : Field K := inferInstance
instance : NumberField K := inferInstance
instance : IsCyclotomicExtension {p} ℚ K :=
  CyclotomicField.isCyclotomicExtension (n := p) (K := ℚ)
instance : IsCMField K :=
  IsCyclotomicExtension.Rat.isCMField K (S := {p}) ⟨p, by simp, hp_gt_two⟩
instance : IsGalois ℚ K := IsCyclotomicExtension.isGalois (n := p) (K := ℚ)

lemma nrComplexPlaces_eq_cyclof :
    InfinitePlace.nrComplexPlaces K = cyclof p := by
  have h_totient : Nat.totient p = p - 1 := Nat.totient_prime hp.1
  have h_complex : InfinitePlace.nrComplexPlaces K = (Nat.totient p) / 2 :=
    IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (n := p) (K := K)
  rw [h_complex, h_totient]; rfl

lemma cyclof_pos : 0 < cyclof p := by dsimp [cyclof]; omega
lemma cyclof_ge_one : 1 ≤ cyclof p := Nat.one_le_of_lt cyclof_pos

/-- The degree [ℚ(ζ_p) : ℚ] = p-1 = totient p. -/
lemma finrank_eq : Module.finrank ℚ K = p - 1 := by
  rw [IsCyclotomicExtension.finrank (S := {p}) (A := ℚ) (B := K)]
  simp [Nat.totient_prime hp.1]

end instances

section exponent_one

/-- In ℚ(ζ_p) for odd prime p, ℤ[ζ_p] is the full ring of integers, so
the Kummer-Dedekind exponent is 1 (applies to all rational primes). -/
lemma exponent_zeta_eq_one :
    RingOfIntegers.exponent ((IsCyclotomicExtension.zeta p ℚ K).toInteger) = 1 := by
  have h_zeta_spec : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p :=
    IsCyclotomicExtension.zeta_spec p ℚ K
  have h_adjoin : Algebra.adjoin ℤ {(h_zeta_spec.toInteger : 𝓞 K)} = ⊤ :=
    IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime h_zeta_spec
  rw [RingOfIntegers.exponent_eq_one_iff]; simpa using h_adjoin

lemma not_dvd_exponent (q : ℕ) [hq_prime : Fact (Nat.Prime q)] : ¬ q ∣
    RingOfIntegers.exponent ((IsCyclotomicExtension.zeta p ℚ K).toInteger) := by
  rw [exponent_zeta_eq_one hp_gt_two]; exact hq_prime.1.not_dvd_one

end exponent_one

section single_prime

/-! ## Step 1: Prime factorization above a rational prime q ≡ 1 (mod p) -/

variable (q : ℕ) [hq_prime : Fact (Nat.Prime q)]
variable (hq_mod : q ≡ 1 [MOD p]) (hq_ne_p : q ≠ p)

include hq_mod hq_ne_p in
/-- The inertial degree of any prime P above (q) in ℚ(ζ_p) is 1 when q ≡ 1 (mod p). -/
lemma inertiaDeg_eq_one (P : Ideal (𝓞 K)) [hP_prime : P.IsPrime] [hP_lies : P.LiesOver (span {(q : ℤ)})] :
    inertiaDeg (span {(q : ℤ)}) P = 1 := by
  have h_not_dvd : ¬ q ∣ p :=
    mt (Nat.Prime.dvd_dvd hq_prime.1 hp.1) hq_ne_p
  have h_inertia := inertiaDeg_eq_of_not_dvd q K P h_not_dvd
  rw [h_inertia]
  have hq_one : (q : ZMod p) = 1 := by
    rw [← ZMod.eq_iff_modEq_nat]; exact hq_mod
  simpa [hq_one] using rfl

include hq_ne_p in
/-- The ramification index of any prime P above (q) in ℚ(ζ_p) is 1 (q ≠ p, unramified). -/
lemma ramificationIdx_eq_one (P : Ideal (𝓞 K)) [hP_prime : P.IsPrime] [hP_lies : P.LiesOver (span {(q : ℤ)})] :
    ramificationIdx (span {(q : ℤ)}) P = 1 := by
  have h_not_dvd : ¬ q ∣ p :=
    mt (Nat.Prime.dvd_dvd hq_prime.1 hp.1) hq_ne_p
  exact ramificationIdx_eq_of_not_dvd q K P h_not_dvd

include hq_mod hq_ne_p in
/-- The number of distinct prime ideals above q in ℚ(ζ_p) is p-1 when q ≡ 1 (mod p).
This follows from the fundamental identity Σ e·f = [K:ℚ] = p-1 with e=f=1 for all primes. -/
lemma card_primesOver_eq :
    Finset.card (IsDedekindDomain.primesOverFinset (Ideal.span {(q : ℤ)}) (𝓞 K)) = p - 1 := by
  have h_max : (Ideal.span {(q : ℤ)} : Ideal ℤ).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime q
  have h_ne_bot : (Ideal.span {(q : ℤ)} : Ideal ℤ) ≠ ⊥ := by simp [NeZero.ne q]
  have h_sum := sum_ramification_inertia (S := 𝓞 K) (R := ℤ) (K := ℚ) (L := K) h_ne_bot
  have h_finrank : Module.finrank ℚ K = p - 1 := finrank_eq hp_gt_two
  rw [h_finrank] at h_sum
  -- Each term e·f = 1
  have h_each_one : ∀ P, P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(q : ℤ)}) (𝓞 K) →
      ramificationIdx (Ideal.span {(q : ℤ)}) P * inertiaDeg (Ideal.span {(q : ℤ)}) P = 1 := by
    intro P hP
    rw [IsDedekindDomain.mem_primesOverFinset_iff h_ne_bot _] at hP
    rcases hP with ⟨hP_prime, hP_lies⟩
    haveI : P.IsPrime := hP_prime
    haveI : P.LiesOver (Ideal.span {(q : ℤ)}) := hP_lies
    rw [ramificationIdx_eq_one hp_gt_two q hq_ne_p P,
      inertiaDeg_eq_one hp_gt_two q hq_mod hq_ne_p P]
    simp
  have h_sum_ones : ∑ P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(q : ℤ)}) (𝓞 K),
      (1 : ℕ) = p - 1 := by
    calc
      _ = ∑ P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(q : ℤ)}) (𝓞 K),
          ramificationIdx (Ideal.span {(q : ℤ)}) P * inertiaDeg (Ideal.span {(q : ℤ)}) P :=
        Finset.sum_congr rfl (fun P hP => by rw [h_each_one P hP])
      _ = Module.finrank ℚ K := h_sum
      _ = p - 1 := h_finrank
  simpa [Finset.sum_const_nsmul] using h_sum_ones

include hq_mod hq_ne_p in
/-- For a prime q ≡ 1 (mod p) (q ≠ p), no prime P above (q) in ℚ(ζ_p)
is fixed by complex conjugation.

**Proof**: If c(P) = P, then the complex conjugation automorphism c ∈ Gal(K/ℚ)
lies in the stabilizer (decomposition group) of P.  But by `card_stabilizer_eq`,
|Stab(P)| = ramificationIdxIn · inertiaDegIn = 1·1 = 1.  Hence Stab(P) = {id}.
Since c ≠ id (p > 2), c ∉ Stab(P), so c(P) ≠ P. -/
lemma conjIdeal_ne_self (P : Ideal (𝓞 K)) [hP_prime : P.IsPrime] [hP_lies : P.LiesOver (Ideal.span {(q : ℤ)})] :
    conjIdeal K P ≠ P := by
  have h_ne_bot : (Ideal.span {(q : ℤ)} : Ideal ℤ) ≠ ⊥ := by simp [NeZero.ne q]
  have h_max_q : (Ideal.span {(q : ℤ)} : Ideal ℤ).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime q
  -- ℚ(ζ_p)/ℚ is a Galois extension.  Let G = Gal(K/ℚ).
  let G : Type _ := Gal(K/ℚ)
  haveI : Finite G := by
    rw [← IsGalois.card_aut_eq_finrank ℚ K]
    exact inferInstance
  haveI : MulSemiringAction G (𝓞 K) :=
    IsGaloisGroup.mulSemiringAction G ℤ (𝓞 K)
  haveI : IsGaloisGroup G ℤ (𝓞 K) :=
    IsGaloisGroup.of_isGalois G K
  -- The decomposition group cardinality: |Stab(P)| = e·f = 1
  have h_stab_card : Nat.card (MulAction.stabilizer G P) = 1 := by
    have h_sep : Algebra.IsSeparable ((ℤ ⧸ Ideal.span {(q : ℤ)}) : Type _) ((𝓞 K) ⧸ P) := by
      -- Finite fields are perfect, so the residue extension is separable
      haveI : Finite ((𝓞 K) ⧸ P) :=
        Ideal.finite_quotient P
      haveI : Finite ((ℤ ⧸ Ideal.span {(q : ℤ)}) : Type _) :=
        Ideal.finite_quotient (Ideal.span {(q : ℤ)})
      exact isSeparable_of_finite _ _
    haveI : P.IsMaximal := IsDedekindDomain.isMaximal_of_isPrime _ hP_prime
    have h_ram_in : (Ideal.span {(q : ℤ)} : Ideal ℤ).ramificationIdxIn (𝓞 K) = 1 := by
      rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(q : ℤ)}) (𝓞 K) P G,
        ramificationIdx_eq_one hp_gt_two q hq_ne_p P]
    have h_inertia_in : (Ideal.span {(q : ℤ)} : Ideal ℤ).inertiaDegIn (𝓞 K) = 1 := by
      rw [Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(q : ℤ)}) (𝓞 K) P G,
        inertiaDeg_eq_one hp_gt_two q hq_mod hq_ne_p P]
    rw [card_stabilizer_eq (Ideal.span {(q : ℤ)}) h_ne_bot P, h_ram_in, h_inertia_in, mul_one]
  -- Complex conjugation c ∈ G = Gal(K/ℚ) is nontrivial (p > 2 ⇒ -1 ≠ 1 mod p)
  let c : G :=
    haveI : IsCMField K := by
      -- Already an instance from the `instances` section
      exact inferInstance
    -- complexConj K is a ℚ-algebra automorphism of K
    (IsCMField.complexConj K).restrictScalars ℚ
  have hc_ne_one : c ≠ 1 := by
    intro hc_eq
    -- If c = id on K, then ζ_p = c(ζ_p) = ζ_p⁻¹, so ζ_p² = 1 → contradiction
    have h_zeta_spec : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p :=
      IsCyclotomicExtension.zeta_spec p ℚ K
    have hc_zeta : c (IsCyclotomicExtension.zeta p ℚ K) = IsCyclotomicExtension.zeta p ℚ K := by
      simpa [hc_eq] using rfl
    have h_conj_zeta : c (IsCyclotomicExtension.zeta p ℚ K) =
        IsCMField.complexConj K (IsCyclotomicExtension.zeta p ℚ K) := rfl
    have h_cm_conj_zeta : IsCMField.complexConj K (IsCyclotomicExtension.zeta p ℚ K) =
        (IsCyclotomicExtension.zeta p ℚ K)⁻¹ := by
      have h_cm_order_two : (IsCMField.complexConj K) ^ 2 = 1 :=
        IsCMField.complexConj_sq K
      have h_zeta_order_p : (IsCyclotomicExtension.zeta p ℚ K) ^ p = 1 :=
        h_zeta_spec.pow_eq_one
      have h_cm_zeta_eq_zeta_inv : IsCMField.complexConj K (IsCyclotomicExtension.zeta p ℚ K) =
          (IsCyclotomicExtension.zeta p ℚ K)⁻¹ := by
        -- This is a key property of CM fields: complex conjugation sends
        -- roots of unity to their inverses.  For cyclotomic fields this holds
        -- by construction of `complexConj`.
        --
        -- In Mathlib, `IsCMField.complexConj` is defined as the unique
        -- K⁺-algebra automorphism sending each complex embedding's generator
        -- to its complex conjugate.  For ℚ(ζ_p), this is the map ζ_p ↦ ζ_p⁻¹.
        simpa using IsCMField.complexConj_zeta_eq_inv K p h_zeta_spec
      simpa [h_cm_conj_zeta, h_cm_zeta_eq_zeta_inv] using hc_zeta
    -- hc_zeta says ζ_p = ζ_p⁻¹, so ζ_p² = 1, contradicting primitivity of ζ_p for p > 2
    have h_zeta_sq_one : (IsCyclotomicExtension.zeta p ℚ K) ^ 2 = 1 := by
      -- From ζ_p = ζ_p⁻¹, multiply both sides by ζ_p
      sorry
    have h_order_dvd_two : p ∣ 2 := h_zeta_spec.orderOf_dvd_of_pow_eq_one 2 h_zeta_sq_one (by norm_num)
    have hp_gt_two' : ¬ p ∣ 2 := by
      have : p > 2 := hp_gt_two
      omega
    exact hp_gt_two' h_order_dvd_two
  -- The key link: conjIdeal corresponds to the action of c on ideals
  have h_conjIdeal_eq_smul : conjIdeal K P = c • P := by
    dsimp [conjIdeal]
    -- c • P = map (galRestrict ℤ ℚ K (𝓞 K) c) P
    -- conjIdeal K P = Ideal.map (ringOfIntegersComplexConj K) P
    -- These are the same map on 𝓞_K because both restrict the same field automorphism
    sorry
  -- Now: if conjIdeal K P = P, then c • P = P, so c ∈ stabilizer G P
  by_contra! h_eq
  rw [h_conjIdeal_eq_smul] at h_eq
  have hc_mem_stab : c ∈ MulAction.stabilizer G P := by
    rw [MulAction.mem_stabilizer_iff]
    exact h_eq
  -- But |Stab(P)| = 1 and 1 ∈ Stab(P), so Stab(P) = {1}
  have h_stab_subsingleton : Subsingleton (MulAction.stabilizer G P) :=
    Nat.card_le_one_iff_subsingleton.mp (by rw [h_stab_card]; exact le_refl _)
  -- But c ≠ 1 and both are in the stabilizer, contradiction
  have h_one_mem : (1 : G) ∈ MulAction.stabilizer G P := by
    rw [MulAction.mem_stabilizer_iff]; simp
  -- c ≠ 1 by hc_ne_one, but both are in the stabilizer which has only 1 element
  have : c = 1 := Subsingleton.elim c 1
  exact hc_ne_one this

end single_prime

section gather_primes

/-! ## Steps 2-4: Gathering split prime pairs from multiple rational primes -/

variable {p}

/-- Given t distinct rational primes q₁,...,q_t ≡ 1 (mod p), select exactly one prime
from each conjugate pair for each qᵢ to obtain `SplitPrimeData K (t * cyclof p)`.

For each qᵢ, there are p-1 prime ideals above qᵢ, which complex conjugation pairs into
(p-1)/2 = cyclof conjugate pairs (none fixed, since `conjIdeal_ne_self`).  We select
one prime from each pair using a Finset-based selection algorithm. -/
def splitPrimeData_from_prime_list (t : ℕ) (qs : List ℕ)
    (hqs_prime : ∀ q ∈ qs, Nat.Prime q)
    (hqs_mod : ∀ q ∈ qs, q ≡ 1 [MOD p])
    (hqs_ne_p : ∀ q ∈ qs, q ≠ p)
    (hqs_nodup : qs.Nodup) :
    SplitPrimeData K (t * cyclof p) := by
  -- This function assembles the split prime data from the list of rational primes.
  -- For each qᵢ ∈ qs:
  --   Let Sᵢ = primesOverFinset (span {(qᵢ : ℤ)}) (𝓞 K)  (size p-1)
  --   Complex conjugation c pairs Sᵢ into (p-1)/2 orbits.
  --   For each orbit {P, c(P)}, select one (say with smaller index in some enumeration).
  -- Collect all selected primes as the output primes.
  --
  -- Total selected: t * cyclof primes (one from each conjugate pair for each rational prime).
  --
  -- Implementation details (to be filled):
  --   1. Enumerate elements of Sᵢ using Finset.sort or Finset.toList
  --   2. For each P, check if P or c(P) has already been added
  --   3. If not, add P (the "first" one encountered)
  sorry

/-- Use Dirichlet's theorem to find t distinct primes q₁, ..., q_t ≡ 1 (mod p),
each ≠ p. -/
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
    -- Find a prime larger than max(qs) that is ≡ 1 mod p
    let max_q := (qs.map id).maximum? |>.getD 0
    rcases Nat.exists_prime_gt_modEq_one max_q hp_pos with ⟨q, hq_prime, hq_gt, hq_mod⟩
    have hq_ne_p : q ≠ p := by
      intro heq; subst heq
      have : p ≡ 1 [MOD p] := by simp [Nat.ModEq, Nat.mod_self]
      -- If p ≡ 1 [MOD p], then p ∣ (1-1) = 0, so p ∣ p.  Not contradictory on its own.
      -- But we chose q > max_q ≥ 0, and q ≠ p holds because if q = p, then
      -- we'd have p ≡ 1 [MOD p], which means p ∣ 0, which is true.  That's not a contradiction.
      -- Instead, note that p ≡ 1 [MOD p] implies p ≡ 1 (mod p), so p mod p = 1 mod p,
      -- so 0 ≡ 1 (mod p), so p ∣ 1, impossible for p > 1.
      have h_mod : p ≡ 1 [MOD p] := by
        -- This follows from `Nat.modEq_self` or similar: p ≡ 0 [MOD p], not 1!
        -- Actually, p ≡ 0 [MOD p], not p ≡ 1 [MOD p].
        -- So Nat.exists_prime_gt_modEq_one cannot return p, since p ≢ 1 [MOD p].
        -- So hq_mod : q ≡ 1 [MOD p] can't hold for q = p.
        -- Let's prove this: if p ≡ 1 [MOD p], then 0 ≡ 1 [MOD p], contradiction.
        rw [Nat.modEq_zero_iff_dvd.mp ?_] at hq_mod
        · omega
        -- Wait, this needs more thought.  Let me just note that p > 1, so p ≡ 0 [MOD p], not 1.
        exact Nat.mod_add_div p 1
      sorry
    have hq_not_mem : q ∉ qs := by
      intro hq_mem
      have hq_bound : q ≤ max_q := by
        rcases List.maximum_of_length_pos ?_ ?_ with h
        sorry
      omega
    refine ⟨q :: qs, by simp [h_len], ?_, ?_, ?_, List.nodup_cons.mpr ⟨hq_not_mem, h_nodup⟩⟩
    · intro r hr; rcases hr with (rfl | hr); exact hq_prime; exact h_prime r hr
    · intro r hr; rcases hr with (rfl | hr); exact hq_mod; exact h_mod r hr
    · intro r hr; rcases hr with (rfl | hr); exact hq_ne_p; exact h_ne_p r hr

end gather_primes

/-- **Main construction**: For K = ℚ(ζ_p) with odd prime p > 2, and any t ∈ ℕ,
construct `SplitPrimeData K (t * ((p-1)/2))` using Dirichlet's theorem
to obtain t distinct rational primes q ≡ 1 (mod p).

This function populates the `splitPrimes` field of `CMTowerData`
when K is a cyclotomic field. -/
def splitPrimeData_of_cyclotomic (t : ℕ) : SplitPrimeData K (t * cyclof p) :=
  let r := find_t_primes_modEq_one hp_gt_two t
  match r with
  | ⟨qs, h_len, h_prime, h_mod, h_ne_p, h_nodup⟩ =>
    splitPrimeData_from_prime_list hp_gt_two t qs h_prime h_mod h_ne_p h_nodup

end Erdos90.CMField.Cyclotomic
