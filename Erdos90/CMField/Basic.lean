import Mathlib

open Real Set NumberField
open scoped Complex Pointwise nonZeroDivisors

noncomputable section

/-!
# CM field arithmetic infrastructure

This file provides the foundation for working with split prime ideal pairs
in CM fields.  The central definition is `SplitPrimeData`, which packages
a collection of prime ideals 𝔭₁, …, 𝔭ₘ in the ring of integers of a CM
field K together with the guarantee that each is distinct from its complex
conjugate.

## Main definitions

* `SplitPrimeData K m` — m distinct prime ideals, each `≠` its complex conjugate,
  all 2m primes (primes and their conjugates) pairwise distinct.
* `conjIdeal` — complex conjugation on `Ideal (𝓞 K)`, defined directly from
  `ringOfIntegersComplexConj`.
-/

variable (K : Type*) [Field K] [NumberField K] [IsCMField K]

/-- Complex conjugation on `Ideal (𝓞 K)`, directly as an `Ideal` map. -/
noncomputable def conjIdeal : Ideal (𝓞 K) → Ideal (𝓞 K) :=
  Ideal.map ((IsCMField.ringOfIntegersComplexConj K).toRingHom)

@[simp]
lemma conjIdeal_mul (I J : Ideal (𝓞 K)) :
    conjIdeal K (I * J) = (conjIdeal K I) * (conjIdeal K J) := by
  simp [conjIdeal, Ideal.map_mul]

@[simp]
lemma conjIdeal_conjIdeal (I : Ideal (𝓞 K)) :
    conjIdeal K (conjIdeal K I) = I := by
  dsimp [conjIdeal]
  let φ : (𝓞 K) →+* (𝓞 K) := (IsCMField.ringOfIntegersComplexConj K).toRingHom
  have h_alg : ∀ x : 𝓞 K, (IsCMField.ringOfIntegersComplexConj K)
      ((IsCMField.ringOfIntegersComplexConj K) x) = x := by
    intro x
    apply RingOfIntegers.ext_iff.mpr
    calc
      ((IsCMField.ringOfIntegersComplexConj K)
          ((IsCMField.ringOfIntegersComplexConj K) x) : K)
          = IsCMField.complexConj K (((IsCMField.ringOfIntegersComplexConj K) x : K)) := by
        rw [IsCMField.coe_ringOfIntegersComplexConj]
      _ = IsCMField.complexConj K (IsCMField.complexConj K (x : K)) := by
        rw [IsCMField.coe_ringOfIntegersComplexConj]
      _ = (x : K) := by rw [IsCMField.complexConj_apply_apply]
  have h_inv : ∀ x : 𝓞 K, φ (φ x) = x := by
    intro x; dsimp [φ]; exact h_alg x
  have h_comp : φ.comp φ = RingHom.id _ :=
    RingHom.ext h_inv
  calc
    Ideal.map φ (Ideal.map φ I) = (I.map φ).map φ := rfl
    _ = I.map (φ.comp φ) := by rw [Ideal.map_map φ φ]
    _ = I.map (RingHom.id _) := by rw [h_comp]
    _ = I := by rw [Ideal.map_id]


lemma conjIdeal_injective : Function.Injective (conjIdeal K) := by
  intro I J h
  apply_fun conjIdeal K at h
  simpa using h

/-- The conjugate of a nonzero prime ideal is again a nonzero prime ideal. -/
lemma conjIdeal_isPrime {P : Ideal (𝓞 K)} (hP : P.IsPrime) :
    (conjIdeal K P).IsPrime := by
  dsimp [conjIdeal]
  haveI : Ideal.IsPrime P := hP
  exact Ideal.map_isPrime_of_equiv (IsCMField.ringOfIntegersComplexConj K)

lemma conjIdeal_ne_bot {P : Ideal (𝓞 K)} (hP : P ≠ ⊥) :
    conjIdeal K P ≠ ⊥ := by
  intro h_eq
  apply hP
  apply conjIdeal_injective K
  rw [h_eq, conjIdeal, Ideal.map_bot]

/-- Data for m split-prime ideal pairs 𝔭ⱼ, c(𝔭ⱼ) in a CM field K.

Each 𝔭ⱼ is a nonzero prime ideal of 𝓞_K, distinct from its complex conjugate,
and all 2m ideals (the primes and their conjugates) are pairwise distinct. -/
structure SplitPrimeData (K : Type*) [Field K] [NumberField K] [IsCMField K] (m : ℕ) where
  /-- The m chosen primes; we take one from each conjugate pair. -/
  primes : Fin m → Ideal (𝓞 K)
  /-- Each prime is nonzero (prime in a Dedekind domain). -/
  h_prime : ∀ j, (primes j).IsPrime
  h_ne_bot : ∀ j, primes j ≠ ⊥
  /-- Each prime is split: it is different from its complex conjugate. -/
  h_split : ∀ j, conjIdeal K (primes j) ≠ primes j
  /-- All 2m primes are pairwise distinct.
  Formally: for i, j, and booleans b₁, b₂ (where `true` = the prime itself,
  `false` = its conjugate), equality of the two ideals forces i = j and b₁ = b₂. -/
  h_distinct : ∀ (i j : Fin m) (b₁ b₂ : Bool),
    (if b₁ then primes i else conjIdeal K (primes i)) =
    (if b₂ then primes j else conjIdeal K (primes j)) →
    i = j ∧ b₁ = b₂

/-- The conjugate prime `c(𝔭ⱼ)` as an ideal. -/
def SplitPrimeData.conjPrime {m : ℕ} (sp : SplitPrimeData K m) (j : Fin m) : Ideal (𝓞 K) :=
  conjIdeal K (sp.primes j)

/-- Convert a `SplitPrimeData` prime to a `HeightOneSpectrum`.
    In a Dedekind domain, nonzero prime ideals are height-1. -/
def SplitPrimeData.toHeightOneSpectrum {m : ℕ} (sp : SplitPrimeData K m)
    (j : Fin m) : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
  ⟨sp.primes j, sp.h_prime j, sp.h_ne_bot j⟩

/-- The conjugate prime as a `HeightOneSpectrum`. -/
def SplitPrimeData.conj_toHeightOneSpectrum {m : ℕ} (sp : SplitPrimeData K m)
    (j : Fin m) : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
  ⟨conjIdeal K (sp.primes j), conjIdeal_isPrime K (sp.h_prime j),
    conjIdeal_ne_bot K (sp.h_ne_bot j)⟩

/-- Conjugate of a `HeightOneSpectrum` under complex conjugation.
    Maps 𝔓 to c(𝔓) = conjIdeal K 𝔓.asIdeal. -/
def conjHeightOneSpectrum (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
  ⟨conjIdeal K v.asIdeal, conjIdeal_isPrime K v.isPrime, conjIdeal_ne_bot K v.ne_bot⟩

@[simp]
lemma conjHeightOneSpectrum_asIdeal (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (conjHeightOneSpectrum K v).asIdeal = conjIdeal K v.asIdeal := rfl

/-- For a nonzero element `a : 𝓞 K`, `count` of `conjIdeal K 𝔓` in the conjugate principal
    ideal `c(a)` equals `count` of `𝔓` in the original principal ideal `(a)`.

    This is the core valuation/count-conjugation lemma.
    Mathematical justification: the ring automorphism `c : 𝓞 K → 𝓞 K` induces a bijection
    on the monoid of nonzero ideals that preserves the factorization into prime ideals
    and maps `𝔓` to `c(𝔓)`. Hence the exponent of `c(𝔓)` in `(c(a))` equals the
    exponent of `𝔓` in `(a)`.

    Reference: Neukirch, Algebraic Number Theory, Proposition I.8.5. -/
lemma count_conj_swap (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (ha : a ≠ 0) :
    FractionalIdeal.count K (conjHeightOneSpectrum K v)
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((IsCMField.ringOfIntegersComplexConj K a : 𝓞 K) : K)) =
    FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)) := by
  sorry

/-- The ideal product J(ε) = ∏_j (if ε_j then 𝔓_j else c(𝔓_j)), as a fractional ideal.
    Defined directly as a FractionalIdeal product for convenient use with `count_prod`. -/
def J_ideal {m : ℕ} (sp : SplitPrimeData K m) (ε : Fin m → Bool) :
    FractionalIdeal (𝓞 K)⁰ K :=
  ∏ j ∈ Finset.univ, (if ε j then (sp.primes j : FractionalIdeal (𝓞 K)⁰ K)
    else (conjIdeal K (sp.primes j) : FractionalIdeal (𝓞 K)⁰ K))

lemma J_ideal_ne_zero {m : ℕ} (sp : SplitPrimeData K m) (ε : Fin m → Bool) :
    J_ideal K sp ε ≠ 0 := by
  dsimp [J_ideal]
  refine Finset.prod_ne_zero_iff.mpr (fun j _ => ?_)
  split
  · exact FractionalIdeal.coeIdeal_ne_zero.mpr (sp.h_ne_bot j)
  · exact FractionalIdeal.coeIdeal_ne_zero.mpr (conjIdeal_ne_bot K (sp.h_ne_bot j))

/-- Helper: `toHeightOneSpectrum i = toHeightOneSpectrum j` implies `i = j`. -/
lemma toHeightOneSpectrum_inj {m : ℕ} (sp : SplitPrimeData K m) {i j : Fin m}
    (h : sp.toHeightOneSpectrum (j := i) = sp.toHeightOneSpectrum (j := j)) : i = j := by
  have h_ideal : sp.primes i = sp.primes j := by
    simpa [SplitPrimeData.toHeightOneSpectrum] using congrArg (fun v => v.asIdeal) h
  have := sp.h_distinct i j true true (by simpa using h_ideal)
  exact this.1

lemma conj_toHeightOneSpectrum_ne_toHeightOneSpectrum {m : ℕ} (sp : SplitPrimeData K m) (i j : Fin m) :
    sp.conj_toHeightOneSpectrum (j := i) ≠ sp.toHeightOneSpectrum (j := j) := by
  intro h
  have h_ideal : conjIdeal K (sp.primes i) = sp.primes j := by
    simpa [SplitPrimeData.conj_toHeightOneSpectrum, SplitPrimeData.toHeightOneSpectrum]
      using congrArg (fun v => v.asIdeal) h
  have hc := sp.h_distinct i j false true (by simpa using h_ideal)
  exact Bool.noConfusion hc.2

/-- For the ideal product `J ε`, the `count` at prime `sp.toHeightOneSpectrum s`
    is 1 if `ε s = true` and 0 otherwise. -/
lemma count_J_eq {m : ℕ} (sp : SplitPrimeData K m) (ε : Fin m → Bool) (s : Fin m) :
    FractionalIdeal.count K (sp.toHeightOneSpectrum (j := s)) (J_ideal K sp ε) =
      if ε s then 1 else 0 := by
  classical
  let v := sp.toHeightOneSpectrum (j := s)
  have hS : ∀ (j : Fin m), (if ε j then (sp.primes j : FractionalIdeal (𝓞 K)⁰ K)
      else (conjIdeal K (sp.primes j) : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 := by
    intro j; split
    · exact FractionalIdeal.coeIdeal_ne_zero.mpr (sp.h_ne_bot j)
    · exact FractionalIdeal.coeIdeal_ne_zero.mpr (conjIdeal_ne_bot K (sp.h_ne_bot j))
  dsimp [J_ideal]
  have hcount := FractionalIdeal.count_prod K v (Finset.univ : Finset (Fin m))
    (fun j => if ε j then (sp.primes j : FractionalIdeal (𝓞 K)⁰ K)
              else (conjIdeal K (sp.primes j) : FractionalIdeal (𝓞 K)⁰ K))
    (fun j hj => hS j)
  rw [hcount]
  have hsum : (∑ j : Fin m,
      FractionalIdeal.count K v (if ε j then (sp.primes j : FractionalIdeal (𝓞 K)⁰ K)
        else (conjIdeal K (sp.primes j) : FractionalIdeal (𝓞 K)⁰ K))) =
      (∑ j : Fin m, if j = s ∧ ε j then (1 : ℤ) else 0) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    cases hεj : ε j
    · -- ε j = false
      simp
      have h_eq : (conjIdeal K (sp.primes j) : FractionalIdeal (𝓞 K)⁰ K) =
          ((sp.conj_toHeightOneSpectrum (j := j)).asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
        simp [SplitPrimeData.conj_toHeightOneSpectrum]
      rw [h_eq]
      have h_ne : sp.conj_toHeightOneSpectrum (j := j) ≠ v :=
        conj_toHeightOneSpectrum_ne_toHeightOneSpectrum (K := K) sp j s
      exact FractionalIdeal.count_maximal_coprime (R := 𝓞 K) (K := K) (v := v)
        (w := sp.conj_toHeightOneSpectrum (j := j)) h_ne
    · -- ε j = true
      simp
      have h_eq : (sp.primes j : FractionalIdeal (𝓞 K)⁰ K) =
          ((sp.toHeightOneSpectrum (j := j)).asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
        simp [SplitPrimeData.toHeightOneSpectrum]
      rw [h_eq]
      rw [FractionalIdeal.count_maximal (R := 𝓞 K) (K := K) (v := v)
        (w := sp.toHeightOneSpectrum (j := j))]
      by_cases hjs : j = s
      · subst hjs; simp [v]
      · have hne : sp.toHeightOneSpectrum (j := j) ≠ v := by
          intro heq; apply hjs; exact toHeightOneSpectrum_inj (K := K) sp heq
        simp [hne, hjs, v]
  rw [hsum]
  rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin m))
    (fun j => if j = s ∧ ε j then (1 : ℤ) else 0) (Finset.mem_univ s)]
  have h_erase : (∑ j ∈ (Finset.univ : Finset (Fin m)).erase s,
      if j = s ∧ ε j then (1 : ℤ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjne : j ≠ s := (Finset.mem_erase.mp hj).1
    simp [hjne]
  rw [h_erase]
  cases ε s <;> simp

/-- For the ideal product `J ε`, the `count` at the conjugate prime
    `conj_toHeightOneSpectrum s` is 1 if `ε s = false` and 0 otherwise. -/
lemma count_J_conj_eq {m : ℕ} (sp : SplitPrimeData K m) (ε : Fin m → Bool) (s : Fin m) :
    FractionalIdeal.count K (sp.conj_toHeightOneSpectrum (j := s)) (J_ideal K sp ε) =
      if ε s then 0 else 1 := by
  classical
  let v := sp.conj_toHeightOneSpectrum (j := s)
  have hS : ∀ (j : Fin m), (if ε j then (sp.primes j : FractionalIdeal (𝓞 K)⁰ K)
      else (conjIdeal K (sp.primes j) : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 := by
    intro j; split
    · exact FractionalIdeal.coeIdeal_ne_zero.mpr (sp.h_ne_bot j)
    · exact FractionalIdeal.coeIdeal_ne_zero.mpr (conjIdeal_ne_bot K (sp.h_ne_bot j))
  dsimp [J_ideal]
  have hcount := FractionalIdeal.count_prod K v (Finset.univ : Finset (Fin m))
    (fun j => if ε j then (sp.primes j : FractionalIdeal (𝓞 K)⁰ K)
              else (conjIdeal K (sp.primes j) : FractionalIdeal (𝓞 K)⁰ K))
    (fun j hj => hS j)
  rw [hcount]
  have hsum : (∑ j : Fin m,
      FractionalIdeal.count K v (if ε j then (sp.primes j : FractionalIdeal (𝓞 K)⁰ K)
        else (conjIdeal K (sp.primes j) : FractionalIdeal (𝓞 K)⁰ K))) =
      (∑ j : Fin m, if j = s ∧ ¬ ε j then (1 : ℤ) else 0) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    cases hεj : ε j
    · -- ε j = false
      simp
      have h_eq : (conjIdeal K (sp.primes j) : FractionalIdeal (𝓞 K)⁰ K) =
          ((sp.conj_toHeightOneSpectrum (j := j)).asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
        simp [SplitPrimeData.conj_toHeightOneSpectrum]
      rw [h_eq]
      rw [FractionalIdeal.count_maximal (R := 𝓞 K) (K := K) (v := v)
        (w := sp.conj_toHeightOneSpectrum (j := j))]
      by_cases hjs : j = s
      · subst hjs; simp [v]
      · have hne : sp.conj_toHeightOneSpectrum (j := j) ≠ v := by
          intro heq; apply hjs
          have h_ideal : conjIdeal K (sp.primes j) = conjIdeal K (sp.primes s) := by
            simpa [SplitPrimeData.conj_toHeightOneSpectrum, v]
              using congrArg (fun v => v.asIdeal) heq
          have h_primes : sp.primes j = sp.primes s := conjIdeal_injective K h_ideal
          have hc := sp.h_distinct j s true true (by simpa using h_primes)
          exact hc.1
        simp [hne, hjs, v]
    · -- ε j = true
      simp
      have h_ne : sp.toHeightOneSpectrum (j := j) ≠ v := by
        intro heq
        have h_ideal : sp.primes j = conjIdeal K (sp.primes s) := by
          simpa [SplitPrimeData.toHeightOneSpectrum, SplitPrimeData.conj_toHeightOneSpectrum, v]
            using congrArg (fun v => v.asIdeal) heq
        have hc := sp.h_distinct j s true false (by simpa using h_ideal)
        exact Bool.noConfusion hc.2
      have h_eq : (sp.primes j : FractionalIdeal (𝓞 K)⁰ K) =
          ((sp.toHeightOneSpectrum (j := j)).asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
        simp [SplitPrimeData.toHeightOneSpectrum]
      rw [h_eq]
      exact FractionalIdeal.count_maximal_coprime (R := 𝓞 K) (K := K) (v := v)
        (w := sp.toHeightOneSpectrum (j := j)) h_ne
  rw [hsum]
  rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin m))
    (fun j => if j = s ∧ ¬ ε j then (1 : ℤ) else 0) (Finset.mem_univ s)]
  have h_erase : (∑ j ∈ (Finset.univ : Finset (Fin m)).erase s,
      if j = s ∧ ¬ ε j then (1 : ℤ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjne : j ≠ s := (Finset.mem_erase.mp hj).1
    simp [hjne]
  rw [h_erase]
  cases ε s <;> simp

/-- For an element γ ∈ K^× fixed by complex conjugation, the `count` at a prime 𝔓
    equals the `count` at the conjugate prime c(𝔓).
    Follows from `count_conj_swap` and the fact that c(γ) = γ. -/
lemma count_eq_count_conj_of_fixed {γ : K} (hγ : γ ≠ 0) (h_fixed : IsCMField.complexConj K γ = γ)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ γ) =
    FractionalIdeal.count K (conjHeightOneSpectrum K v)
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ γ) := by
  sorry

end
