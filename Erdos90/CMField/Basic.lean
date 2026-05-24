import Mathlib

open Real Set NumberField
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

end
