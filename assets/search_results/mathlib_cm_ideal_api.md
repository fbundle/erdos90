# Mathlib v4.29.1 — CM Field and Ideal APIs (Complete Audit)

Sources:
- vendor/mathlib4/Mathlib/NumberTheory/NumberField/CMField.lean
- vendor/mathlib4/Mathlib/RingTheory/ClassGroup.lean
- vendor/mathlib4/Mathlib/NumberTheory/NumberField/ClassNumber.lean
- vendor/mathlib4/Mathlib/NumberTheory/RamificationInertia/*.lean
- vendor/mathlib4/Mathlib/RingTheory/Ideal/Norm/RelNorm.lean

---

## A. IsCMField API — AVAILABLE

```lean
-- Class definition (CMField.lean)
class IsCMField (K : Type*) [Field K] [NumberField K] extends
  IsTotallyComplex K, IsQuadraticExtension (maximalRealSubfield K) K

-- Complex conjugation
IsCMField.complexConj (K : Type*) [Field K] [NumberField K] [IsCMField K] :
    K ≃ₐ[maximalRealSubfield K] K

-- Key: embedding of α/c(α) has norm 1
IsCMField.complexEmbedding_complexConj (K : Type*) [Field K] [NumberField K] [IsCMField K]
    (φ : K →+* ℂ) (x : K) :
    φ (complexConj K x) = starRingEnd ℂ (φ x)

-- Galois structure
IsCMField.isConj_complexConj (φ : K →+* ℂ) : IsConj φ (complexConj K)

-- Fixed-field characterization (KEY for hmk_unit_inj step 4)
IsCMField.complexConj_eq_self_iff (K : Type*) [Field K] [NumberField K] [IsCMField K] (x : K) :
    complexConj K x = x ↔ x ∈ maximalRealSubfield K

-- Integer-ring version
IsCMField.RingOfIntegers.complexConj_eq_self_iff (x : 𝓞 K) :
    (complexConj K : 𝓞 K →+* 𝓞 K) x = x ↔ x ∈ RingOfIntegers.maximalRealSubfield K

-- Units and torsion
IsCMField.unitsMulComplexConjInv (K) : (𝓞 K)ˣ →* torsion K
IsCMField.unitsMulComplexConjInv_ker (K) : (unitsMulComplexConjInv K).ker = realUnits K

-- Cyclotomic fields are CM (KEY instance)
IsCyclotomicExtension.Rat.isCMField {S : Set ℕ} (hS : ∃ n ∈ S, 2 < n)
    [IsCyclotomicExtension S ℚ K] : IsCMField K
```

---

## B. ClassGroup API — AVAILABLE

```lean
-- Definition (ClassGroup.lean)
ClassGroup R  -- quotient of nonzero fractional ideals by principals

-- Fintype instance (needed for card bounds)
NumberField.RingOfIntegers.instFintypeClassGroup : Fintype (ClassGroup (𝓞 K))

-- Class number
NumberField.classNumber K : ℕ = Fintype.card (ClassGroup (𝓞 K))

-- Surjectivity: every class contains an integral ideal
ClassGroup.mk0_surjective : Function.Surjective (ClassGroup.mk0 (R₀ := 𝓞 K))

-- Same class iff differ by principal
ClassGroup.mk0_eq_mk0_iff {I J : (Ideal (𝓞 K))⁰} :
    ClassGroup.mk0 I = ClassGroup.mk0 J ↔
    ∃ x : (𝓞 K)×, (I : Ideal (𝓞 K)) = ↑x • (J : Ideal (𝓞 K))

-- Minkowski bound representative (KEY for Prop 2.2 cardinality)
NumberField.exists_ideal_in_class_of_norm_le (C : ClassGroup (𝓞 K)) :
    ∃ I : Ideal (𝓞 K), ClassGroup.mk0 ⟨I, _⟩ = C ∧ Ideal.absNorm I ≤ ⌊M K⌋₊

-- Principal ideal detection
ClassGroup.mk_eq_one_iff {I : FractionalIdeal (𝓞 K)⁰ K} :
    ClassGroup.mk I = 1 ↔ I.IsPrincipal
```

---

## C. Ramification / Split Prime API — PARTIALLY AVAILABLE

```lean
-- Ramification index and inertia degree (Basic.lean)
Ideal.ramificationIdx (f : R →+* S) (p : Ideal R) (P : Ideal S) : ℕ
Ideal.inertiaDeg (f : R →+* S) (p : Ideal R) (P : Ideal S) : ℕ

-- Galois-equivariant versions (Galois.lean)
Ideal.ramificationIdxIn (p : Ideal R) (B : Type*) (G : Type*) : ℕ
Ideal.inertiaDegIn (p : Ideal R) (B : Type*) (G : Type*) : ℕ

-- Fundamental identity: |primesOver| * e * f = [L:K]
ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (hp : p.IsMaximal) ... : (primesOver p B).ncard * e * f = Module.finrank K L

-- LiesOver relation
class Ideal.LiesOver (P : Ideal B) (p : Ideal R) : Prop
Ideal.LiesOver.mk (h : p = P.under A) : P.LiesOver p

-- Primes over a given prime
Ideal.primesOver (p : Ideal R) (B : Type*) : Set (Ideal B)
IsDedekindDomain.primesOverFinset (p : Ideal R) (S : Finset (Ideal R)) : Finset (Ideal B)

-- Kummer-Dedekind splitting
NumberField.Ideal.KummerDedekind.primesOverSpanEquivMonicFactorsMod :
    Equiv (primesOver (Ideal.span {p}) B) {f : ... | ...}
```

**MISSING**: No `IsTotallySplit`, no `IsSplit` predicate, no direct "p splits completely in K/F" API. Must use `ramificationIdxIn = 1 ∧ inertiaDegIn = 1 ∧ (primesOver p B).ncard = [K:F]`.

---

## D. Ideal Relative Norm — AVAILABLE

```lean
-- Relative norm as an ideal map (RelNorm.lean)
Ideal.relNorm (R : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    Ideal S →*₀ Ideal R

-- Multiplicativity
Ideal.relNorm_mul (I J : Ideal S) : relNorm R (I * J) = relNorm R I * relNorm R J

-- Galois invariance
Ideal.relNorm_smul (g : G) (I : Ideal S) : relNorm R (g • I) = relNorm R I
```

**MISSING**: No theorem `Ideal.relNorm_of_prime_above`: given 𝔓 lying over 𝔭 with ramificationIdx = 1 and inertiaDeg = 1, prove `relNorm R 𝔓 = 𝔭`. Needs to be assembled from `ramificationIdx` + `inertiaDeg` + `IsDedekindDomain.prod_ramificationIdx_pow`.

---

## E. What Is Missing for the Three Sorries

### For `hΛ_inj` (gs_tower_levels)

Root cause: no CM field K of degree 2f from a Golod-Shafarevich tower.
- **Missing**: `exists_gs_cm_field (f : ℕ) (hf : f ≥ 1) : ∃ K, [Field K] ∧ [IsCMField K] ∧ Module.finrank ℚ K = 2 * f`
- The Minkowski lattice infrastructure (cmMinkowskiLattice) is ready; just needs K.
- hΛ_inj then follows: `v ∈ Λ → v = Φ(a)` for `a : 𝓞 K`, and `Φ(a)(fin0) = σ₁(a) = 0 → a = 0` by injectivity of field embedding σ₁.

### For `hmk_unit_norm`

Requires:
1. K (same as above)
2. Split primes 𝔓₁,...,𝔓_m: use Chebotarev (missing) or Kummer-Dedekind (partial)
3. J₁·J₂⁻¹ = (α): use `ClassGroup.mk0_eq_mk0_iff.mp`
4. α/c(α) has norm 1: apply `cm_norm_div_conj_eq_one` (ALREADY PROVED)
5. Bridge to Fin f → ℂ: use `mixedSpace_equiv_pi_fin_of_card` (ALREADY PROVED)

### For `hmk_unit_inj`

Requires:
1. α₁₂/α₁₃ ∈ K⁺: use `IsCMField.complexConj_eq_self_iff` (AVAILABLE)
2. Ideal factorization: J₁₂ = (β)·J₁₃ with β ∈ K⁺× → same element of L
   - Needs ideal splitting at each 𝔓_j (missing `relNorm_of_prime_above` + factorization)
3. β = ±1 (unit): needs `IsTotallyReal (maximalRealSubfield K)` + unit bound

---

## F. Recommended Addition to Mathlib

The minimal addition needed:

```lean
-- CM field of prescribed degree from cyclotomic tower
theorem exists_cm_field_of_degree (f : ℕ) (hf : f ≥ 1) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K),
      Module.finrank ℚ K = 2 * f := by
  -- Use Bertrand's postulate to find prime p with 2f < p ≤ 4f
  -- Then K = CyclotomicField p ℚ has degree φ(p) = p-1 ≥ 2f
  -- Alternatively: take p = 2f+1 if prime (Sophie Germain primes exist for small f)
  sorry  -- Requires Bertrand + IsCyclotomicExtension degree formula

-- Split prime existence for cyclotomic K
theorem exists_split_primes_for_cm (K : Type*) [Field K] [NumberField K] [IsCMField K]
    (m : ℕ) : ∃ (S : Finset (Ideal (𝓞 K))), S.card = m ∧
      ∀ 𝔓 ∈ S, 𝔓.IsMaximal ∧ Ideal.ramificationIdx (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) (𝔓.under _) 𝔓 = 1 := by
  -- Chebotarev density: infinitely many primes split completely in K/K⁺
  sorry  -- Requires Chebotarev density theorem (not in Mathlib v4.29.1)
```
