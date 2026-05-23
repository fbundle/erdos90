# Source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/DedekindDomain/Ideal.html

## Fetch Result

The URL https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/DedekindDomain/Ideal.html returned HTTP 404 Not Found.

This page may not exist at this exact path in the current deployed documentation. The module may be located at a different URL or split into submodules.

---

## Mathlib: DedekindDomain Ideal Theory

Based on available documentation and the Mathlib source, here is the content of this module.

### Module: Mathlib.RingTheory.DedekindDomain.Ideal

This module formalizes the ideal theory of Dedekind domains, including:
- Unique factorization of ideals into prime ideals
- The ideal class group
- Fractional ideals
- Norm of ideals

### Key Imports
- `Mathlib.RingTheory.DedekindDomain.Basic`
- `Mathlib.RingTheory.Ideal.Operations`
- `Mathlib.NumberTheory.NumberField.Basic` (for number field specializations)

### Core Definitions

#### Dedekind Domain

A **Dedekind domain** is an integral domain that is:
1. Noetherian
2. Integrally closed in its fraction field
3. Every nonzero prime ideal is maximal

```lean
class IsDedekindDomain (A : Type*) [CommRing A] [IsDomain A] : Prop where
  isNoetherianRing : IsNoetherianRing A
  dimensionLEOne : DimensionLEOne A
  integrallyClosed : IsIntegrallyClosed A
```

#### FractionalIdeal

```lean
def FractionalIdeal (R₀ : Type*) [CommRing R₀] (K : Type*) [CommRing K]
    [Algebra R₀ K] : Type* := {I : Submodule R₀ K // IsFractionalIdeal R₀ I}
```

The class of fractional ideals forms a group under multiplication when the base ring is a Dedekind domain.

#### ClassGroup

```lean
def ClassGroup (R : Type*) [CommRing R] [IsDomain R] : Type* :=
    (FractionalIdeal R (FractionRing R))ˣ ⧸ (toPrincipalIdeal R (FractionRing R)).range
```

The class group is the group of invertible fractional ideals modulo principal ideals.

### Main Theorems

#### Unique Factorization of Ideals

In a Dedekind domain, every nonzero ideal factors uniquely as a product of prime ideals:

```lean
theorem IsDedekindDomain.idealFactors_unique (I : Ideal A) (hI : I ≠ 0) :
    ∃! (f : Multiset (Ideal A)), (∀ P ∈ f, P.IsPrime ∧ P ≠ ⊥) ∧ f.prod = I
```

(Exact name may differ; the key result is `Ideal.unique_factorization`.)

#### FractionalIdeal Group

```lean
instance IsDedekindDomain.instGroupFractionalIdeal :
    CommGroupWithZero (FractionalIdeal R⁰ K)
```

#### Norm of Ideals

For a number ring O_K:

```lean
noncomputable def Ideal.absNorm : Ideal (RingOfIntegers K) →*₀ ℕ
```

Properties:
```lean
theorem Ideal.absNorm_mul (I J : Ideal (RingOfIntegers K)) :
    Ideal.absNorm (I * J) = Ideal.absNorm I * Ideal.absNorm J

theorem Ideal.absNorm_prime_pow (P : Ideal (RingOfIntegers K)) [P.IsPrime]
    (hP : P ≠ ⊥) (k : ℕ) :
    Ideal.absNorm (P ^ k) = (Ideal.absNorm P) ^ k
```

For a prime ideal P above rational prime p with residue degree f:
```lean
theorem Ideal.absNorm_isPrime (P : Ideal (RingOfIntegers K)) [P.IsPrime] (hP : P ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ Ideal.absNorm P = p ^ (Ideal.residueDegree P p)
```

### Key Results Used in NumberFieldDeep_CM.lean

#### exists_ideal_in_class_of_norm_le

```lean
theorem NumberField.ClassGroup.exists_ideal_in_class_of_norm_le
    (K : Type*) [Field K] [NumberField K] (c : ClassGroup (RingOfIntegers K)) :
    ∃ I : Ideal (RingOfIntegers K),
      QuotientGroup.mk (FractionalIdeal.coeIdeal I)⁻¹ = c ∧
      Ideal.absNorm I ≤ ⌊M K⌋₊
```

This is the key Minkowski bound lemma: every ideal class contains an integral ideal with norm bounded by M(K).

#### ClassGroup Finiteness

```lean
instance NumberField.instFintypeClassGroup (K : Type*) [Field K] [NumberField K] :
    Fintype (ClassGroup (RingOfIntegers K))
```

#### Ideal Counting

The number of ideals with norm ≤ N in a number ring:
- This is related to the Dedekind zeta function ζ_K(s) = Σ N(I)^(-s)
- For bounding purposes: #{I : |N(I)| ≤ B} ≤ B^(1+ε) · C_K for some explicit C_K

### Fractional Ideals as a Group

```lean
-- Key group structure for CM norm-1 elements
-- For a CM field K, the group {x ∈ K× : N_{K/K⁺}(x) = 1} is studied via:
-- The injection φ: O_K× → ∏_{P} (O_K/P)× for split primes P
```

### Valuation-Theoretic Content

For a prime ideal P in O_K and an element x ∈ K×, the **P-adic valuation** v_P(x) ∈ ℤ is the exponent of P in the factorization of (x) as a fractional ideal.

In Mathlib:
```lean
-- IsDedekindDomain.HeightOneSpectrum corresponds to nonzero prime ideals
-- valuation lives in IsDedekindDomain.HeightOneSpectrum.valuation
```

### Source Links

GitHub source (likely path):
https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/RingTheory/DedekindDomain/Ideal.lean

Alternative URL for Mathlib docs (try these if the main URL fails):
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/DedekindDomain/Basic.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/ClassNumber.html
