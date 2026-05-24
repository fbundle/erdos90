import Mathlib

open Real Set
open scoped Complex Pointwise

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
* `conjHeightOneSpectrum` — complex conjugation lifted to `HeightOneSpectrum (𝓞 K)`.
* `conjIdeal` — complex conjugation on `Ideal (𝓞 K)`, defined directly from
  `ringOfIntegersComplexConj`.
-/

variable (K : Type*) [Field K] [NumberField K] [IsCMField K]

/-- Complex conjugation on `HeightOneSpectrum (𝓞 K)`, induced by
`IsCMField.ringOfIntegersComplexConj`. -/
noncomputable def conjHeightOneSpectrum :
    HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K) :=
  HeightOneSpectrum.equivOfRingEquiv
    (IsCMField.ringOfIntegersComplexConj K).toRingEquiv

@[simp]
lemma conjHeightOneSpectrum_asIdeal (v : HeightOneSpectrum (𝓞 K)) :
    (conjHeightOneSpectrum K v).asIdeal =
      Ideal.map (IsCMField.ringOfIntegersComplexConj K) v.asIdeal := by
  rfl

lemma conjHeightOneSpectrum_involutive :
    Function.Involutive (conjHeightOneSpectrum K) := by
  intro v
  ext : 1
  simp [conjHeightOneSpectrum]

/-- Complex conjugation on `Ideal (𝓞 K)`, directly as an `Ideal` map. -/
noncomputable def conjIdeal : Ideal (𝓞 K) → Ideal (𝓞 K) :=
  Ideal.map (IsCMField.ringOfIntegersComplexConj K)

@[simp]
lemma conjIdeal_mul (I J : Ideal (𝓞 K)) :
    conjIdeal K (I * J) = (conjIdeal K I) * (conjIdeal K J) := by
  simp [conjIdeal, Ideal.map_mul]

@[simp]
lemma conjIdeal_conjIdeal (I : Ideal (𝓞 K)) :
    conjIdeal K (conjIdeal K I) = I := by
  dsimp [conjIdeal]
  rw [Ideal.map_map, Ideal.map_id]
  · rfl
  · -- ringOfIntegersComplexConj composed with itself is identity
    apply AlgEquiv.coe_ringEquiv_injective
    ext x; simp

lemma conjIdeal_injective : Function.Injective (conjIdeal K) := by
  intro I J h
  apply_fun conjIdeal K at h
  simpa using h

/-- The conjugate of a nonzero prime ideal is again a nonzero prime ideal. -/
lemma conjIdeal_isPrime {P : Ideal (𝓞 K)} (hP : P.IsPrime) :
    (conjIdeal K P).IsPrime := by
  rw [conjIdeal]
  exact Ideal.map_isPrime_of_equiv
    (IsCMField.ringOfIntegersComplexConj K).toRingEquiv hP

lemma conjIdeal_ne_bot {P : Ideal (𝓞 K)} (hP : P ≠ ⊥) :
    conjIdeal K P ≠ ⊥ := by
  contrapose! hP
  apply_fun conjIdeal K at hP
  simpa using hP

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

/-- The total number of ideals in the set {𝔭ⱼ, c(𝔭ⱼ) : j < m} is 2×m, all distinct. -/
lemma SplitPrimeData.card_total {m : ℕ} (sp : SplitPrimeData K m) :
    Fintype.card { I : Ideal (𝓞 K) // ∃ (j : Fin m) (b : Bool),
      I = if b then sp.primes j else sp.conjPrime j } = 2 * m := by
  classical
    have h_total : Fintype.card (Fin m × Bool) = 2 * m := by simp
    refine (Fintype.card_congr ?_).trans h_total
    apply Equiv.ofBijective
      (λ ⟨j, b⟩ => ⟨if b then sp.primes j else sp.conjPrime j, ⟨j, b, rfl⟩⟩)
    constructor
    · rintro ⟨j₁, b₁⟩ ⟨j₂, b₂⟩ h_eq
      have h_type_eq := congrArg Subtype.val h_eq
      simp only at h_type_eq
      have h_res := sp.h_distinct j₁ j₂ b₁ b₂ h_type_eq
      exact Prod.ext (Fin.ext h_res.1) (Bool.ext h_res.2)
    · rintro ⟨I, ⟨j, b, hI⟩⟩
      exact ⟨⟨j, b⟩, by ext; exact hI⟩

end
