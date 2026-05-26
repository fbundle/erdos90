import Mathlib
import Erdos90.CMField.Basic

open Set Polynomial NumberField Ideal
open scoped BigOperators Complex Pointwise

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

/-- f = (p-1)/2 = nrComplexPlaces. -/
abbrev cyclof : ℕ := (p - 1) / 2

local notation "K" => CyclotomicField p ℚ

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

/-- Section-level instances that typeclass search can find. -/
instance isScalarTower_ℤ_ℚ_K : IsScalarTower ℤ ℚ K :=
  IsScalarTower.of_algebraMap_eq (fun x => by simp)
instance isScalarTower_ℤ_𝓞K_K : IsScalarTower ℤ (𝓞 K) K :=
  IsScalarTower.of_algebraMap_eq (fun x => by
    unfold RingOfIntegers; rfl)
instance isGaloisGroup_ℤ_𝓞K : IsGaloisGroup (K ≃ₐ[ℚ] K) ℤ (𝓞 K) := by
  infer_instance
instance : FiniteDimensional ℚ K :=
  IsCyclotomicExtension.finiteDimensional {p} ℚ K

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

omit hp_gt_two in lemma inertiaDeg_eq_one (hq_mod : q ≡ 1 [MOD p]) (hq_ne_p : q ≠ p)
    (P : Ideal (𝓞 K)) [hP_prime : P.IsPrime]
    [hP_lies : P.LiesOver (span {(q : ℤ)})] :
    inertiaDeg (span {(q : ℤ)}) P = 1 := by
    have hq_not_dvd_p : ¬ q ∣ p := by
      rw [Nat.prime_dvd_prime_iff_eq hq_prime.1 hp.1]
      exact hq_ne_p
    have h_inertia := IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd q K P hq_not_dvd_p
    rw [h_inertia]
    have hq_mod_zmod : (q : ZMod p) = 1 := by
      simpa using (ZMod.natCast_eq_natCast_iff q 1 p).mpr hq_mod
    rw [hq_mod_zmod, orderOf_one]

omit hp_gt_two in lemma ramificationIdx_eq_one (hq_ne_p : q ≠ p)
    (P : Ideal (𝓞 K)) [hP_prime : P.IsPrime]
    [hP_lies : P.LiesOver (span {(q : ℤ)})] :
    ramificationIdx (span {(q : ℤ)}) P = 1 := by
    have hq_not_dvd_p : ¬ q ∣ p := by
      rw [Nat.prime_dvd_prime_iff_eq hq_prime.1 hp.1]
      exact hq_ne_p
    exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd q K P hq_not_dvd_p

omit hp_gt_two in lemma card_primesOver_eq (hq_mod : q ≡ 1 [MOD p]) (hq_ne_p : q ≠ p) :
    Finset.card (IsDedekindDomain.primesOverFinset (Ideal.span {(q : ℤ)}) (𝓞 K)) = p - 1 := by
    letI : Fact (Nat.Prime q) := hq_prime
    set span_q := Ideal.span {(q : ℤ)} with hspan_q
    have h_span_ne_bot : span_q ≠ ⊥ := by
      rw [hspan_q]
      exact mt Ideal.span_singleton_eq_bot.mp
        (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hq_prime.1))
    haveI : span_q.IsMaximal := by
      have : Fact (Nat.Prime q) := hq_prime
      infer_instance
    have h_finrank : Module.finrank ℚ K = p - 1 := by
      haveI : NeZero p := NeZero.of_pos (Nat.Prime.pos hp.1)
      have h := IsCyclotomicExtension.finrank K
        (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (a := p)))
      rw [h, Nat.totient_prime hp.1]
    let i_st1 : IsScalarTower ℤ ℚ K := AddCommGroup.intIsScalarTower (R := ℚ) (M := K)
    let i_st2 : IsScalarTower ℤ (𝓞 K) K := AddCommGroup.intIsScalarTower (R := 𝓞 K) (M := K)
    have h_sum_eq : (∑ P ∈ IsDedekindDomain.primesOverFinset span_q (𝓞 K),
        span_q.ramificationIdx P * span_q.inertiaDeg P) = Module.finrank ℚ K :=
      @Ideal.sum_ramification_inertia ℤ _ (𝓞 K) _ _ _ ℚ K
        _ _ _ _ _ _ _ _ _ i_st2 i_st1 _ span_q _ h_span_ne_bot
    have h_each_eq_one : ∀ P ∈ IsDedekindDomain.primesOverFinset span_q (𝓞 K),
        span_q.ramificationIdx P * span_q.inertiaDeg P = 1 := by
      intro P hPmem
      have hP_mem' : P ∈ Ideal.primesOver span_q (𝓞 K) :=
        ((IsDedekindDomain.mem_primesOverFinset_iff h_span_ne_bot (B := 𝓞 K)).mp hPmem)
      haveI : P.IsPrime := hP_mem'.1
      haveI : P.LiesOver span_q := hP_mem'.2
      rw [ramificationIdx_eq_one p q hq_ne_p P,
        inertiaDeg_eq_one p q hq_mod hq_ne_p P,
        one_mul]
    have hcard : Finset.card (IsDedekindDomain.primesOverFinset span_q (𝓞 K)) = Module.finrank ℚ K := by
      calc
        Finset.card (IsDedekindDomain.primesOverFinset span_q (𝓞 K))
            = (∑ P ∈ IsDedekindDomain.primesOverFinset span_q (𝓞 K), 1) := by simp
        _ = (∑ P ∈ IsDedekindDomain.primesOverFinset span_q (𝓞 K),
            span_q.ramificationIdx P * span_q.inertiaDeg P) := by
          rw [Finset.sum_congr rfl (fun P hP => (h_each_eq_one P hP).symm)]
        _ = Module.finrank ℚ K := h_sum_eq
    simpa [hspan_q, h_finrank] using hcard

lemma conjIdeal_ne_self (hq_mod : q ≡ 1 [MOD p]) (hq_ne_p : q ≠ p)
    (P : Ideal (𝓞 K)) [hP_prime : P.IsPrime]
    [hP_lies : P.LiesOver (Ideal.span {(q : ℤ)})] :
    conjIdeal K P ≠ P := by
  set span_q := Ideal.span {(q : ℤ)} with hspan_q
  have h_span_ne_bot : span_q ≠ ⊥ := by
    rw [hspan_q]
    exact mt Ideal.span_singleton_eq_bot.mp
      (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hq_prime.1))
  haveI : span_q.IsMaximal := by
    have : Fact (Nat.Prime q) := hq_prime
    infer_instance
  have hq_not_dvd_p : ¬ q ∣ p := by
    rw [Nat.prime_dvd_prime_iff_eq hq_prime.1 hp.1]
    exact hq_ne_p
  have h_ramIn : span_q.ramificationIdxIn (𝓞 K) = 1 :=
    IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd q K hq_not_dvd_p
  have h_inertiaIn : span_q.inertiaDegIn (𝓞 K) = 1 := by
    have h := IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd q K hq_not_dvd_p
    rw [h]
    have hq_mod_zmod : (q : ZMod p) = 1 := by
      simpa using (ZMod.natCast_eq_natCast_iff q 1 p).mpr hq_mod
    rw [hq_mod_zmod, orderOf_one]
  have hP_ne_bot : P ≠ ⊥ :=
    ne_bot_of_liesOver_of_ne_bot h_span_ne_bot P
  haveI : P.IsMaximal :=
    hP_prime.isMaximal hP_ne_bot
  -- Set up the finite field structure and separability
  have h_sep : Algebra.IsSeparable (ℤ ⧸ span_q) (𝓞 K ⧸ P) := by
    letI : Field (ℤ ⧸ span_q) := Ideal.Quotient.field span_q
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    haveI : Finite (ℤ ⧸ span_q) :=
      Ring.HasFiniteQuotients.finiteQuotient (I := span_q) h_span_ne_bot
    haveI : Finite (𝓞 K ⧸ P) :=
      Ring.HasFiniteQuotients.finiteQuotient (I := P) hP_ne_bot
    haveI : PerfectField (ℤ ⧸ span_q) := PerfectField.ofFinite
    haveI : Module.Finite (ℤ ⧸ span_q) (𝓞 K ⧸ P) :=
      ((Module.finite_iff_finite (R := ℤ ⧸ span_q)).mpr inferInstance)
    haveI : Algebra.IsAlgebraic (ℤ ⧸ span_q) (𝓞 K ⧸ P) :=
      Algebra.IsAlgebraic.of_finite (ℤ ⧸ span_q) (𝓞 K ⧸ P)
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : FiniteDimensional ℚ K :=
    IsCyclotomicExtension.finiteDimensional {p} ℚ K
  haveI : Algebra.IsAlgebraic ℚ K :=
    Algebra.IsAlgebraic.of_finite ℚ K
  -- The stabilizer has cardinality e·f = 1
  -- We use the orbit-stabilizer theorem:
  -- |G| = |Orbit(P)| * |Stab(P)|, with |G| = p-1 and |Orbit(P)| = p-1 (all primes over q)
  haveI : Algebra.IsSeparable (ℤ ⧸ span_q) (𝓞 K ⧸ P) := h_sep
  haveI : FiniteDimensional ℚ K :=
    IsCyclotomicExtension.finiteDimensional {p} ℚ K
  haveI : IsScalarTower ℤ ℚ K := isScalarTower_ℤ_ℚ_K (p := p)
  haveI : IsScalarTower ℤ (𝓞 K) K := isScalarTower_ℤ_𝓞K_K (p := p)
  haveI : IsGaloisGroup (K ≃ₐ[ℚ] K) ℤ (𝓞 K) := isGaloisGroup_ℤ_𝓞K (p := p)
  haveI : Finite (K ≃ₐ[ℚ] K) := inferInstance
  have h_stab_card : Nat.card (MulAction.stabilizer (K ≃ₐ[ℚ] K) P) = 1 := by
    have h := Ideal.card_stabilizer_eq (R := ℤ) (S := 𝓞 K) (G := K ≃ₐ[ℚ] K)
      (p := span_q) (hp := h_span_ne_bot) (P := P)
    rw [h_ramIn, h_inertiaIn, mul_one] at h
    exact h
  -- Complex conjugation as an element of the Galois group Gal(K/ℚ)
  let σ : (K ≃ₐ[ℚ] K) := (IsCMField.complexConj K).restrictScalars ℚ
  have hσ_ne_one : σ ≠ 1 := by
    intro h_eq
    have h_conj_eq_one : IsCMField.complexConj K = 1 := by
      ext x
      have h := congrArg (fun (f : K ≃ₐ[ℚ] K) => f x) h_eq
      simpa [σ] using h
    exact IsCMField.complexConj_ne_one K h_conj_eq_one
  -- Key: σ • P = conjIdeal K P
  have h_σ_action : σ • P = conjIdeal K P := by
    calc
      σ • P = P.map (MulSemiringAction.toRingHom (K ≃ₐ[ℚ] K) (𝓞 K) σ) := by
        rw [pointwise_smul_def]
      _ = P.map ((IsCMField.ringOfIntegersComplexConj K).toRingHom) := by
        have h_eq_ringHom : MulSemiringAction.toRingHom (K ≃ₐ[ℚ] K) (𝓞 K) σ =
            (IsCMField.ringOfIntegersComplexConj K).toRingHom := by
          refine RingHom.ext fun x => ?_
          apply RingOfIntegers.ext
          calc
            ((MulSemiringAction.toRingHom (K ≃ₐ[ℚ] K) (𝓞 K) σ) x : K) = (σ • (x : K)) := rfl
            _ = (((IsCMField.ringOfIntegersComplexConj K).toRingHom) x : K) := by
              dsimp [σ, IsCMField.ringOfIntegersComplexConj]
        rw [h_eq_ringHom]
      _ = conjIdeal K P := by dsimp [conjIdeal]
  -- Assume conjIdeal K P = P and derive a contradiction
  intro h_eq
  -- Then σ • P = P
  have hσ_stab : σ • P = P := by
    rw [h_σ_action, h_eq]
  have hσ_mem : σ ∈ MulAction.stabilizer (K ≃ₐ[ℚ] K) P := by
    rw [MulAction.mem_stabilizer_iff, hσ_stab]
  -- The stabilizer has Nat.card = 1, so it's the trivial subgroup
  haveI : Finite (MulAction.stabilizer (K ≃ₐ[ℚ] K) P) := by
    haveI : Fintype (K ≃ₐ[ℚ] K) := Fintype.ofFinite (K ≃ₐ[ℚ] K)
    infer_instance
  have h_stab_eq_bot : MulAction.stabilizer (K ≃ₐ[ℚ] K) P = ⊥ :=
    (MulAction.stabilizer (K ≃ₐ[ℚ] K) P).eq_bot_of_card_eq h_stab_card
  -- Therefore σ = 1, contradiction
  have hσ_eq_one : σ = 1 := by
    have : σ ∈ (⊥ : Subgroup (K ≃ₐ[ℚ] K)) := h_stab_eq_bot ▸ hσ_mem
    simpa [Subgroup.mem_bot] using this
  exact hσ_ne_one hσ_eq_one

end factorization_lemmas

/-!
## Main construction
-/

/-- Given t distinct rational primes q₁,...,q_t ≡ 1 (mod p), select exactly one prime
from each conjugate pair for each qᵢ to obtain `SplitPrimeData K (t * cyclof p)`. -/
def splitPrimeData_from_prime_list (t : ℕ) (qs : List ℕ)
    (_hqs_len : qs.length = t)
    (_hqs_prime : ∀ q ∈ qs, Nat.Prime q)
    (_hqs_mod : ∀ q ∈ qs, q ≡ 1 [MOD p])
    (_hqs_ne_p : ∀ q ∈ qs, q ≠ p)
    (_hqs_nodup : qs.Nodup) :
    SplitPrimeData K (t * cyclof p) := by
  let m := t * cyclof p
  -- Build the full set of prime ideals over all q ∈ qs, then pick one from each
  -- conjugacy orbit.  Since everything is classical, we use `Classical.choice` on
  -- an existence proof.
  have h_exists : Nonempty (SplitPrimeData K m) := by
    -- Helper: given a Finset S closed under conjIdeal K with no fixed points,
    -- there exists T ⊆ S containing exactly one from each {P, conjIdeal K P} orbit.
    have h_transversal (S : Finset (Ideal (𝓞 K)))
        (h_closed : ∀ P ∈ S, conjIdeal K P ∈ S)
        (h_no_fix : ∀ P ∈ S, conjIdeal K P ≠ P) :
        ∃ (T : Finset (Ideal (𝓞 K))),
          T ⊆ S ∧
          (∀ P ∈ S, P ∈ T ∨ conjIdeal K P ∈ T) ∧
          (∀ P ∈ T, conjIdeal K P ∉ T) := by
      -- Put `h_no_fix` into the induction motive so it's available for the current set
      revert h_no_fix
      refine Finset.induction_on S (fun h_no_fix => ⟨∅, Finset.Subset.refl _, (by simp), (by simp)⟩)
        (fun a S' haS' IH h_no_fix => ?_)
      have h_no_fix_a : conjIdeal K a ≠ a := h_no_fix a (Finset.mem_insert_self _ _)
      have h_no_fix' : ∀ P ∈ S', conjIdeal K P ≠ P :=
        fun P hP => h_no_fix P (Finset.mem_insert_of_mem hP)
      rcases IH h_no_fix' with ⟨T, hT_sub, hT_cover, hT_no_conj⟩
      by_cases ha_conj : a ∈ T.image (conjIdeal K)
      · -- a is conjugate of something already in T; skip it
        refine ⟨T, Finset.Subset.trans hT_sub (Finset.subset_insert _ _), ?_, hT_no_conj⟩
        intro P hP
        rcases Finset.mem_insert.mp hP with (rfl | hP')
        · rcases Finset.mem_image.mp ha_conj with ⟨Q, hQ, h_eq⟩
          right; rw [← h_eq, conjIdeal_conjIdeal]; exact hQ
        · exact hT_cover P hP'
      · -- a is not a conjugate of anything in T; add it
        refine ⟨insert a T, Finset.insert_subset_insert a hT_sub, ?_, ?_⟩
        · intro P hP
          rcases Finset.mem_insert.mp hP with (rfl | hP')
          · left; exact Finset.mem_insert_self _ _
          · rcases hT_cover P hP' with (h | h)
            · left; exact Finset.mem_insert_of_mem h
            · right; exact Finset.mem_insert_of_mem h
        · intro P hP
          rcases Finset.mem_insert.mp hP with (h_eq_P | hP')
          · -- h_eq_P : P = a
            rw [h_eq_P]
            intro h_conj
            rcases Finset.mem_insert.mp h_conj with (h_eq_conj | h_conj')
            · exact h_no_fix_a h_eq_conj
            · apply ha_conj
              apply Finset.mem_image.mpr
              exact ⟨conjIdeal K a, h_conj', conjIdeal_conjIdeal K a⟩
          · -- hP' : P ∈ T
            intro h_conj
            rcases Finset.mem_insert.mp h_conj with (h_eq_conj | h_conj')
            · apply ha_conj
              apply Finset.mem_image.mpr
              exact ⟨P, hP', h_eq_conj⟩
            · exact hT_no_conj P hP' h_conj'

    -- Given a transversal T of S where S.card = 2*k, prove T.card = k.
    have h_card_transversal (S T : Finset (Ideal (𝓞 K)))
        (hT_sub : T ⊆ S)
        (h_closed : ∀ P ∈ S, conjIdeal K P ∈ S)
        (hT_cover : ∀ P ∈ S, P ∈ T ∨ conjIdeal K P ∈ T)
        (hT_no_conj : ∀ P ∈ T, conjIdeal K P ∉ T) :
        T.card * 2 = S.card := by
      -- The map P ↦ conjIdeal K P is a bijection from T to S \ T
      have h_image_eq : T.image (conjIdeal K) = S \ T := by
        apply Finset.Subset.antisymm
        · intro x hx
          rcases Finset.mem_image.mp hx with ⟨P, hP, rfl⟩
          refine Finset.mem_sdiff.mpr ⟨h_closed P (hT_sub hP), hT_no_conj P hP⟩
        · intro x hx
          have hxS : x ∈ S := Finset.mem_sdiff.mp hx |>.1
          have hx_not_T : x ∉ T := Finset.mem_sdiff.mp hx |>.2
          rcases hT_cover x hxS with (hxT | h_conj_T)
          · exact absurd hxT hx_not_T
          · apply Finset.mem_image.mpr
            exact ⟨conjIdeal K x, h_conj_T, conjIdeal_conjIdeal K x⟩
      have h_image_card : (T.image (conjIdeal K)).card = T.card :=
        Finset.card_image_of_injective T (conjIdeal_injective K)
      rw [h_image_eq] at h_image_card
      have h_sdiff_add := Finset.card_sdiff_add_card_eq_card hT_sub
      omega

    -- Now collect all primes over all q ∈ qs.
    -- For each q, the primesOverFinset has size 2*cyclof p and is closed under conjIdeal.
    have h_per_q (q : ℕ) (hq_mem : q ∈ qs) :
        ∃ (T : Finset (Ideal (𝓞 K))),
          T.card = cyclof p ∧
          (∀ P ∈ T, P.IsPrime) ∧
          (∀ P ∈ T, P ≠ ⊥) ∧
          (∀ P ∈ T, conjIdeal K P ≠ P) ∧
          (∀ P ∈ T, conjIdeal K P ∉ T) := by
      have hq_prime : Fact (Nat.Prime q) := ⟨_hqs_prime q hq_mem⟩
      have hq_mod : q ≡ 1 [MOD p] := _hqs_mod q hq_mem
      have hq_ne_p : q ≠ p := _hqs_ne_p q hq_mem
      haveI : Fact (Nat.Prime q) := hq_prime
      let span_q := Ideal.span {(q : ℤ)}
      have h_span_ne_bot : span_q ≠ ⊥ :=
        mt Ideal.span_singleton_eq_bot.mp
          (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hq_prime.1))
      haveI : span_q.IsMaximal := by infer_instance
      let S := IsDedekindDomain.primesOverFinset span_q (𝓞 K)
      have hS_card : S.card = 2 * cyclof p := by
        rw [card_primesOver_eq p q hq_mod hq_ne_p]
        dsimp [cyclof]
        have hp_gt_2 : 2 < p := hp_gt_two.out
        have h_dvd : 2 ∣ p - 1 := by
          have h_cases := hp.1.eq_two_or_odd
          rcases h_cases with (h_eq | h_mod)
          · omega
          · -- h_mod : p % 2 = 1
            have h_eq_p : p = 2 * (p / 2) + 1 :=
              calc
                p = 2 * (p / 2) + p % 2 := by rw [Nat.div_add_mod p 2]
                _ = 2 * (p / 2) + 1 := by rw [h_mod]
            have : p - 1 = 2 * (p / 2) := by omega
            rw [this]
            exact ⟨p / 2, rfl⟩
        exact (Nat.mul_div_cancel' h_dvd).symm
      have hS_closed : ∀ P ∈ S, conjIdeal K P ∈ S := by
        intro P hP
        have hP_mem' : P ∈ Ideal.primesOver span_q (𝓞 K) :=
          ((IsDedekindDomain.mem_primesOverFinset_iff h_span_ne_bot (B := 𝓞 K)).mp hP)
        haveI : P.IsPrime := hP_mem'.1
        haveI : P.LiesOver span_q := hP_mem'.2
        haveI : (conjIdeal K P).IsPrime := conjIdeal_isPrime K hP_mem'.1
        haveI : (conjIdeal K P).LiesOver span_q := by
          dsimp [conjIdeal]
          let σ : 𝓞 K ≃ₐ[ℤ] 𝓞 K := (IsCMField.ringOfIntegersComplexConj K).restrictScalars ℤ
          have h := Ideal.map_equiv_liesOver (A := ℤ) (B := 𝓞 K) (C := 𝓞 K) (P := P) (p := span_q) (σ := σ)
          simpa [σ] using h
        apply (IsDedekindDomain.mem_primesOverFinset_iff h_span_ne_bot (B := 𝓞 K)).mpr
        exact ⟨inferInstance, inferInstance⟩
      have hS_no_fix : ∀ P ∈ S, conjIdeal K P ≠ P := by
        intro P hP
        have hP_mem' : P ∈ Ideal.primesOver span_q (𝓞 K) :=
          ((IsDedekindDomain.mem_primesOverFinset_iff h_span_ne_bot (B := 𝓞 K)).mp hP)
        haveI : P.IsPrime := hP_mem'.1
        haveI : P.LiesOver span_q := hP_mem'.2
        exact conjIdeal_ne_self p q hq_mod hq_ne_p P
      rcases h_transversal S hS_closed hS_no_fix with ⟨T, hT_sub, hT_cover, hT_no_conj⟩
      have hT_card : T.card = cyclof p := by
        have h := h_card_transversal S T hT_sub hS_closed hT_cover hT_no_conj
        rw [hS_card] at h
        omega
      have hT_prime : ∀ P ∈ T, P.IsPrime := by
        intro P hP
        have hP_mem' : P ∈ Ideal.primesOver span_q (𝓞 K) :=
          ((IsDedekindDomain.mem_primesOverFinset_iff h_span_ne_bot (B := 𝓞 K)).mp
            (hT_sub hP))
        exact hP_mem'.1
      have hT_ne_bot : ∀ P ∈ T, P ≠ ⊥ := by
        intro P hP
        have hP_mem_set : P ∈ Ideal.primesOver span_q (𝓞 K) := by
          apply (IsDedekindDomain.mem_primesOverFinset_iff h_span_ne_bot (B := 𝓞 K)).mp
          exact hT_sub hP
        haveI : P.IsPrime := hP_mem_set.1
        haveI : P.LiesOver span_q := hP_mem_set.2
        exact Ideal.ne_bot_of_mem_primesOver h_span_ne_bot hP_mem_set
      have hT_split : ∀ P ∈ T, conjIdeal K P ≠ P := by
        intro P hP
        have hP_mem' : P ∈ Ideal.primesOver span_q (𝓞 K) :=
          ((IsDedekindDomain.mem_primesOverFinset_iff h_span_ne_bot (B := 𝓞 K)).mp
            (hT_sub hP))
        haveI : P.IsPrime := hP_mem'.1
        haveI : P.LiesOver span_q := hP_mem'.2
        exact conjIdeal_ne_self p q hq_mod hq_ne_p P
      exact ⟨T, hT_card, hT_prime, hT_ne_bot, hT_split, hT_no_conj⟩

    -- Build the big Finset U of ALL prime ideals over all q ∈ qs.
    -- Each q ∈ qs contributes 2*cyclof p primes (forming cyclof p conjugate pairs).
    -- The sets for different q are disjoint, so |U| = t * 2 * cyclof p = 2*m.
    -- Then pick a transversal of the involution conjIdeal K on U.
    let U := Finset.biUnion qs.toFinset
      (fun q => IsDedekindDomain.primesOverFinset (Ideal.span {(q : ℤ)}) (𝓞 K))

    -- |U| = 2*m
    have hU_card : U.card = 2 * m := by
      dsimp [U, m]
      have h_each_card (q : ℕ) (hq_mem : q ∈ qs.toFinset) :
          (IsDedekindDomain.primesOverFinset (Ideal.span {(q : ℤ)}) (𝓞 K)).card = 2 * cyclof p := by
        have hq_mem' : q ∈ qs := by simpa using hq_mem
        haveI : Fact (Nat.Prime q) := ⟨_hqs_prime q hq_mem'⟩
        rw [card_primesOver_eq p q (_hqs_mod q hq_mem') (_hqs_ne_p q hq_mem')]
        dsimp [cyclof]
        have hp_gt_2 : 2 < p := hp_gt_two.out
        have h_dvd : 2 ∣ p - 1 := by
          have h_cases := hp.1.eq_two_or_odd
          rcases h_cases with (h_eq | h_mod)
          · omega
          · have : p - 1 = 2 * (p / 2) := by
              have h_eq_p : p = 2 * (p / 2) + p % 2 := by rw [Nat.div_add_mod p 2]
              rw [h_mod] at h_eq_p
              omega
            rw [this]
            exact ⟨p / 2, rfl⟩
        exact (Nat.mul_div_cancel' h_dvd).symm
      have h_disjoint : (qs.toFinset : Set ℕ).PairwiseDisjoint
          (fun (q : ℕ) => IsDedekindDomain.primesOverFinset (Ideal.span {(q : ℤ)}) (𝓞 K)) := by
        intro q₁ hq₁ q₂ hq₂ hne
        have hq₁_mem' : q₁ ∈ qs := by simpa using hq₁
        have hq₂_mem' : q₂ ∈ qs := by simpa using hq₂
        haveI hq₁_prime : Fact (Nat.Prime q₁) := ⟨_hqs_prime q₁ hq₁_mem'⟩
        haveI hq₂_prime : Fact (Nat.Prime q₂) := ⟨_hqs_prime q₂ hq₂_mem'⟩
        let span_q₁ := Ideal.span {(q₁ : ℤ)}
        let span_q₂ := Ideal.span {(q₂ : ℤ)}
        have h_span_q₁_ne_bot : span_q₁ ≠ ⊥ := by
          dsimp [span_q₁]
          exact mt Ideal.span_singleton_eq_bot.mp
            (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hq₁_prime.1))
        have h_span_q₂_ne_bot : span_q₂ ≠ ⊥ := by
          dsimp [span_q₂]
          exact mt Ideal.span_singleton_eq_bot.mp
            (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hq₂_prime.1))
        change Disjoint (IsDedekindDomain.primesOverFinset (Ideal.span {(q₁ : ℤ)}) (𝓞 K))
          (IsDedekindDomain.primesOverFinset (Ideal.span {(q₂ : ℤ)}) (𝓞 K))
        rw [Finset.disjoint_iff_inter_eq_empty]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro P hP
        rcases Finset.mem_inter.mp hP with ⟨hP₁, hP₂⟩
        have hP₁_mem' : P ∈ Ideal.primesOver span_q₁ (𝓞 K) :=
          ((IsDedekindDomain.mem_primesOverFinset_iff h_span_q₁_ne_bot (B := 𝓞 K)).mp hP₁)
        have hP₂_mem' : P ∈ Ideal.primesOver span_q₂ (𝓞 K) :=
          ((IsDedekindDomain.mem_primesOverFinset_iff h_span_q₂_ne_bot (B := 𝓞 K)).mp hP₂)
        have h_span_eq : span_q₁ = span_q₂ := by
          rw [hP₁_mem'.2.over, hP₂_mem'.2.over]
        have h_associated : Associated (q₁ : ℤ) (q₂ : ℤ) :=
          ((Ideal.span_singleton_eq_span_singleton (x := (q₁ : ℤ)) (y := (q₂ : ℤ))).mp h_span_eq)
        have h_natAbs_eq : (q₁ : ℤ).natAbs = (q₂ : ℤ).natAbs :=
          (Int.natAbs_eq_iff_associated.mpr h_associated)
        have h_eq : q₁ = q₂ := by
          simpa using h_natAbs_eq
        exact hne h_eq
      rw [Finset.card_biUnion h_disjoint]
      calc
        (∑ q ∈ qs.toFinset, (IsDedekindDomain.primesOverFinset
            (Ideal.span {(q : ℤ)}) (𝓞 K)).card)
            = (∑ q ∈ qs.toFinset, (2 * cyclof p)) :=
          Finset.sum_congr rfl (fun q hq => by rw [h_each_card q hq])
        _ = qs.toFinset.card * (2 * cyclof p) := by simp
        _ = (t : ℕ) * (2 * cyclof p) := by
          rw [List.toFinset_card_of_nodup _hqs_nodup, _hqs_len]
        _ = 2 * (t * cyclof p) := by
          rw [← Nat.mul_assoc, Nat.mul_comm t 2, Nat.mul_assoc]

    -- U is closed under conjIdeal K
    have hU_closed : ∀ P ∈ U, conjIdeal K P ∈ U := by
      intro P hP
      rcases Finset.mem_biUnion.mp hP with ⟨q, hq_mem, hP_mem⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨q, hq_mem, ?_⟩
      have hq_mem' : q ∈ qs := by
        simpa using hq_mem
      have hq_prime : Fact (Nat.Prime q) := ⟨_hqs_prime q hq_mem'⟩
      haveI : Fact (Nat.Prime q) := hq_prime
      let span_q := Ideal.span {(q : ℤ)}
      have h_span_ne_bot : span_q ≠ ⊥ :=
        mt Ideal.span_singleton_eq_bot.mp
          (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hq_prime.1))
      let S := IsDedekindDomain.primesOverFinset span_q (𝓞 K)
      have hS_closed : ∀ P ∈ S, conjIdeal K P ∈ S := by
        intro P hP_S
        have hP_mem' : P ∈ Ideal.primesOver span_q (𝓞 K) :=
          ((IsDedekindDomain.mem_primesOverFinset_iff h_span_ne_bot (B := 𝓞 K)).mp hP_S)
        haveI : P.IsPrime := hP_mem'.1
        haveI : P.LiesOver span_q := hP_mem'.2
        haveI : (conjIdeal K P).IsPrime := conjIdeal_isPrime K hP_mem'.1
        haveI : (conjIdeal K P).LiesOver span_q := by
          dsimp [conjIdeal]
          let σ : 𝓞 K ≃ₐ[ℤ] 𝓞 K := (IsCMField.ringOfIntegersComplexConj K).restrictScalars ℤ
          have h := Ideal.map_equiv_liesOver (A := ℤ) (B := 𝓞 K) (C := 𝓞 K) (P := P) (p := span_q) (σ := σ)
          simpa [σ] using h
        apply (IsDedekindDomain.mem_primesOverFinset_iff h_span_ne_bot (B := 𝓞 K)).mpr
        exact ⟨inferInstance, inferInstance⟩
      exact hS_closed P hP_mem

    -- conjIdeal K has no fixed points in U
    have hU_no_fix : ∀ P ∈ U, conjIdeal K P ≠ P := by
      intro P hP
      rcases Finset.mem_biUnion.mp hP with ⟨q, hq_mem, hP_mem⟩
      have hq_mem' : q ∈ qs := by
        simpa using hq_mem
      have hq_prime : Fact (Nat.Prime q) := ⟨_hqs_prime q hq_mem'⟩
      have hq_mod : q ≡ 1 [MOD p] := _hqs_mod q hq_mem'
      have hq_ne_p : q ≠ p := _hqs_ne_p q hq_mem'
      haveI : Fact (Nat.Prime q) := hq_prime
      let span_q := Ideal.span {(q : ℤ)}
      have h_span_ne_bot : span_q ≠ ⊥ :=
        mt Ideal.span_singleton_eq_bot.mp
          (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hq_prime.1))
      have hP_mem' : P ∈ Ideal.primesOver span_q (𝓞 K) :=
        ((IsDedekindDomain.mem_primesOverFinset_iff h_span_ne_bot (B := 𝓞 K)).mp hP_mem)
      haveI : P.IsPrime := hP_mem'.1
      haveI : P.LiesOver span_q := hP_mem'.2
      exact conjIdeal_ne_self p q hq_mod hq_ne_p P

    -- Get a transversal of the involution on U
    rcases h_transversal U hU_closed hU_no_fix with ⟨T, hT_sub, hT_cover, hT_no_conj⟩

    -- By the cardinality lemma, T.card = |U|/2 = m
    have hT_card : T.card = m := by
      have h := h_card_transversal U T hT_sub hU_closed hT_cover hT_no_conj
      rw [hU_card] at h
      omega

    -- Each element of T is prime (since U consists of primes)
    have hT_prime : ∀ P ∈ T, P.IsPrime := by
      intro P hP
      have hP_U : P ∈ U := hT_sub hP
      rcases Finset.mem_biUnion.mp hP_U with ⟨q, hq_mem, hP_mem⟩
      have hq_mem' : q ∈ qs := by
        simpa using hq_mem
      have hq_prime : Fact (Nat.Prime q) := ⟨_hqs_prime q hq_mem'⟩
      haveI : Fact (Nat.Prime q) := hq_prime
      let span_q := Ideal.span {(q : ℤ)}
      have h_span_ne_bot : span_q ≠ ⊥ :=
        mt Ideal.span_singleton_eq_bot.mp
          (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hq_prime.1))
      have hP_mem' : P ∈ Ideal.primesOver span_q (𝓞 K) :=
        ((IsDedekindDomain.mem_primesOverFinset_iff h_span_ne_bot (B := 𝓞 K)).mp hP_mem)
      exact hP_mem'.1

    -- Each element of T is nonzero
    have hT_ne_bot : ∀ P ∈ T, P ≠ ⊥ := by
      intro P hP
      have hP_U : P ∈ U := hT_sub hP
      rcases Finset.mem_biUnion.mp hP_U with ⟨q, hq_mem, hP_mem⟩
      have hq_mem' : q ∈ qs := by
        simpa using hq_mem
      have hq_prime : Fact (Nat.Prime q) := ⟨_hqs_prime q hq_mem'⟩
      haveI : Fact (Nat.Prime q) := hq_prime
      let span_q := Ideal.span {(q : ℤ)}
      have h_span_ne_bot : span_q ≠ ⊥ :=
        mt Ideal.span_singleton_eq_bot.mp
          (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hq_prime.1))
      have hP_mem' : P ∈ Ideal.primesOver span_q (𝓞 K) :=
        ((IsDedekindDomain.mem_primesOverFinset_iff h_span_ne_bot (B := 𝓞 K)).mp hP_mem)
      exact Ideal.ne_bot_of_mem_primesOver h_span_ne_bot hP_mem'

    -- Each element of T is different from its conjugate
    have hT_split : ∀ P ∈ T, conjIdeal K P ≠ P :=
      fun P hP => hU_no_fix P (hT_sub hP)

    -- Get a Fin m enumeration of T using cardinality equivalence
    have h_equiv : (T : Type _) ≃ Fin m := by
      apply Fintype.equivFinOfCardEq
      simp [hT_card]

    -- Define primes from the enumeration
    let primes (j : Fin m) : Ideal (𝓞 K) := (h_equiv.symm j).val

    -- Compute Q = product of the rational primes qs
    let Q : ℕ := qs.prod
    have h_Q_pos : Q > 0 := by
      refine List.prod_pos (fun q hq => Nat.Prime.pos (_hqs_prime q hq))
    refine ⟨primes, ?_, ?_, ?_, ?_, Q, h_Q_pos, ?_, ?_⟩
    · -- h_prime
      intro j
      dsimp [primes]
      exact hT_prime (h_equiv.symm j).val (Subtype.mem _)
    · -- h_ne_bot
      intro j
      dsimp [primes]
      exact hT_ne_bot (h_equiv.symm j).val (Subtype.mem _)
    · -- h_split
      intro j
      dsimp [primes]
      exact hT_split (h_equiv.symm j).val (Subtype.mem _)
    · -- h_distinct: all 2m primes are pairwise distinct
      intro i j b₁ b₂ h_eq
      have h_primes_mem_T (k : Fin m) : primes k ∈ T := by
        dsimp [primes]
        exact (h_equiv.symm k).property
      have h_conj_not_mem_T (k : Fin m) : conjIdeal K (primes k) ∉ T := by
        dsimp [primes]
        exact hT_no_conj (h_equiv.symm k).val (h_equiv.symm k).property
      by_cases hb₁ : b₁
      · rw [if_pos hb₁] at h_eq
        by_cases hb₂ : b₂
        · rw [if_pos hb₂] at h_eq
          have h_primes_eq : primes i = primes j := h_eq
          have h_sub_eq : h_equiv.symm i = h_equiv.symm j := by
            apply Subtype.ext
            dsimp [primes] at h_primes_eq
            exact h_primes_eq
          have hi_eq_j : i = j := h_equiv.symm.injective h_sub_eq
          exact ⟨hi_eq_j, by simp [hb₁, hb₂]⟩
        · rw [if_neg hb₂] at h_eq
          exfalso
          apply h_conj_not_mem_T j
          rw [← h_eq]
          exact h_primes_mem_T i
      · rw [if_neg hb₁] at h_eq
        by_cases hb₂ : b₂
        · rw [if_pos hb₂] at h_eq
          exfalso
          apply h_conj_not_mem_T i
          rw [h_eq]
          exact h_primes_mem_T j
        · rw [if_neg hb₂] at h_eq
          have h_conj_eq : conjIdeal K (primes i) = conjIdeal K (primes j) := h_eq
          have h_primes_eq : primes i = primes j := conjIdeal_injective K h_conj_eq
          have h_sub_eq : h_equiv.symm i = h_equiv.symm j := by
            apply Subtype.ext
            dsimp [primes] at h_primes_eq
            exact h_primes_eq
          have hi_eq_j : i = j := h_equiv.symm.injective h_sub_eq
          exact ⟨hi_eq_j, by simp [hb₁, hb₂]⟩
    · -- h_Q_count_at_split: count K 𝔓_j (Q) = 1 for each split prime
      -- TRUE: each 𝔓_j lies over exactly one q_j ∈ qs with `ramificationIdx = 1`
      -- (from `ramificationIdx_eq_one`, this file lines 144-165), and the primes
      -- in qs are pairwise distinct (h_distinct), so v_{𝔓_j}(Q) = v_{𝔓_j}(q_j) = 1.
      -- Filling this requires bridging `count K v (span q)` with `ramificationIdx`,
      -- which is a separate Mathlib-API exercise (see Phase B note in CLAUDE.md).
      intro j
      sorry
    · -- h_Q_count_at_conj: count K c(𝔓_j) (Q) = 1 for each conjugate split prime
      -- TRUE by the same argument: c(𝔓_j) lies over q_j with `ramificationIdx = 1`.
      intro j
      sorry
  exact Classical.choice h_exists

/-- **Main construction**: For K = ℚ(ζ_p) with odd prime p > 2, and any t ∈ ℕ,
construct `SplitPrimeData K (t * ((p-1)/2))` using Dirichlet's theorem. -/
def splitPrimeData_of_cyclotomic (t : ℕ) : SplitPrimeData K (t * cyclof p) :=
  let r := find_t_primes_modEq_one (p := p) t
  let qs := Classical.choose r
  let h_spec := Classical.choose_spec r
  splitPrimeData_from_prime_list (p := p) t qs
    (h_spec.1) (h_spec.2.1) (h_spec.2.2.1) (h_spec.2.2.2.1) (h_spec.2.2.2.2)

end Erdos90.CMField.Cyclotomic
