# Mathlib v4.30.0-rc2 — Valuation and Dedekind Domain APIs

Source: grep of `vendor/mathlib4/` (May 2026 snapshot)

---

## 1. `IsDedekindDomain.HeightOneSpectrum` (the key structure)

**File**: `Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean` (line 495)

```lean
structure HeightOneSpectrum where
  asIdeal : Ideal R
  isPrime  : asIdeal.IsPrime
  ne_bot   : asIdeal ≠ ⊥
```

Indexes height-1 (= maximal, in Dedekind domains) prime ideals.

---

## 2. `IsDedekindDomain.HeightOneSpectrum.valuation` (THE KEY API)

**File**: `Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` (line 298)

```lean
def IsDedekindDomain.HeightOneSpectrum.valuation
    (v : HeightOneSpectrum R) : Valuation K ℤᵐ⁰
```

The **adic valuation** on the fraction field K associated to the prime ideal v.asIdeal. This is the valuation needed for all three sorries:
- `v_{𝔓_s}(u_ε) = 2(ε_s − η_s)` is a statement about this valuation
- Key lemma: `valuation_eq_intValuationDef` and `intValuation_eq_pow_neg_ofAdd`

---

## 3. `IsDiscreteValuationRing`

**File**: `Mathlib/RingTheory/DiscreteValuationRing/Basic.lean` (line 58)

```lean
class IsDiscreteValuationRing (R : Type u) [CommRing R] [IsDomain R] : Prop
  extends IsPrincipalIdealRing R, IsLocalRing R where
  not_a_field' : maximalIdeal R ≠ ⊥
```

The localization of 𝓞_K at a prime 𝔓 is a DVR; this provides the local-ring structure for valuation arguments.

---

## 4. `Ideal.LiesOver`

**File**: `Mathlib/RingTheory/Ideal/Over.lean` (line 116)

```lean
@[mk_iff] class LiesOver : Prop where
  over : p = P.under A
```

The "P lies over p" predicate. Needed to express that 𝔓_s lies over q_s.

---

## 5. `FractionalIdeal.spanSingleton`

**File**: `Mathlib/RingTheory/FractionalIdeal/Operations.lean` (line 565)

```lean
irreducible_def spanSingleton (x : P) : FractionalIdeal S P
```

The principal fractional ideal (x) = span{x}. Used in:
`ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring` to extract α from class equality.

---

## 6. `ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring` (CONFIRMED AVAILABLE)

**File**: `Mathlib/RingTheory/ClassGroup.lean` (line 267)

```lean
theorem ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring
    [IsDedekindDomain R] {I J : (Ideal R)⁰} :
    ClassGroup.mk0 I = ClassGroup.mk0 J ↔
    ∃ (x : _) (_ : x ≠ (0 : K)), spanSingleton R⁰ x * I = J
```

This is already used in `h_exists_alpha` in `NumberFieldDeep_CM.lean`.

---

## 7. `maximalRealSubfield` (CONFIRMED AVAILABLE)

**File**: `Mathlib/NumberTheory/NumberField/InfinitePlace/TotallyRealComplex.lean` (line 125)

```lean
def maximalRealSubfield : Subfield K where
  carrier := {x | ∀ φ : K →+* ℂ, star (φ x) = φ x}
```

The totally real subfield K⁺ ⊂ K: elements fixed by all complex conjugations.

---

## 8. `IsCMField.complexConj` (CONFIRMED AVAILABLE)

**File**: `Mathlib/NumberTheory/NumberField/CMField.lean` (line 143)

```lean
noncomputable def complexConj : K ≃ₐ[K⁺] K
```

The unique nontrivial K⁺-automorphism of K.

---

## What Is Missing for the Valuation Argument

### Missing: valuation of a product ideal

We need: `v_{𝔓}(I · J) = v_{𝔓}(I) + v_{𝔓}(J)` for fractional ideals I, J.
This likely follows from `IsDedekindDomain.HeightOneSpectrum.valuation` applied to
the generators, but requires assembling:
- `intValuation_mul` or similar
- The fact that v(α) = v((α)) (valuation of element = valuation of principal ideal)

### Missing: `v_{𝔓_s}(c(α)) = v_{c𝔓_s}(α)` (conjugation swaps valuations)

In a CM field K with complex conjugation c:
- v_{c𝔓}(α) = v_{𝔓}(c(α)) for any α ∈ K×

This uses the Galois-equivariance of valuations:
- `Ideal.HeightOneSpectrum` has no direct `galois_action_valuation` lemma
- Could be proved from: if σ : K → K is a field automorphism, then v_{σ𝔓}(α) = v_{𝔓}(σ⁻¹ α)
- Applied with σ = complexConj: v_{c𝔓}(α) = v_{𝔓}(c⁻¹ α) = v_{𝔓}(c α) (since c² = id)

### Missing: formula `v_{𝔓_s}(𝔄_ε)`

The ideal 𝔄_ε = ∏_{ε_s=1} 𝔓_s · ∏_{ε_s=0} c𝔓_s gives:
```
v_{𝔓_s}(𝔄_ε) = ε_s   (since 𝔓_s appears with multiplicity ε_s ∈ {0,1})
```
This requires that 𝔓_s and c𝔓_s are distinct primes (which holds since q_s splits in K, i.e., 𝔓_s ≠ c𝔓_s), and the unique factorization of ideals in Dedekind domains.

Available: `IsDedekindDomain.factorization` — the prime factorization of ideals in a Dedekind domain.

---

## Recommended Approach for the Sorries

Given the missing Galois-equivariance lemma, the most Lean-feasible approach is:

1. **Add a sorry'd helper** `v_conj_swap : ∀ (α : K) (𝔓 : HeightOneSpectrum (𝓞 K)), (HeightOneSpectrum.mk (conjIdeal 𝔓.asIdeal) ...).valuation K α = 𝔓.valuation K (complexConj K α)` — this is a standard ANT fact (Neukirch I.8.3).

2. **Use `IsDedekindDomain.factorization_eq`** to compute v_{𝔓_s}(𝔄_ε) = ε_s from the definition of 𝔄_ε.

3. **Chain**: v_{𝔓_s}(u_ε) = v_{𝔓_s}(α_ε) − v_{𝔓_s}(c(α_ε)) = v_{𝔓_s}(α_ε) − v_{c𝔓_s}(α_ε) = (ε_s − η_s) − (1−ε_s − (1−η_s)) = 2(ε_s − η_s).
