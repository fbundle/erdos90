# Source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/Norm.html

## Module: Mathlib.NumberTheory.NumberField.Norm

### Overview

This Mathlib module defines the norm morphism for rings of integers in finite extensions of number fields, and proves its key properties.

### Imports

```
Init
Mathlib.NumberTheory.NumberField.Basic
Mathlib.RingTheory.Localization.NormTrace
Mathlib.RingTheory.Norm.Transitivity
```

### Main Definitions

#### RingOfIntegers.norm K

Presents the algebraic norm as a monoid homomorphism between rings of integers:

```lean
noncomputable def RingOfIntegers.norm (K : Type*) {L : Type*} [Field K] [Field L]
    [Algebra K L] [IsIntegralClosure (𝓞 K) ℤ K] [IsIntegralClosure (𝓞 L) ℤ L]
    [FiniteDimensional K L] : (𝓞 L) →* (𝓞 K)
```

This is the restriction of `Algebra.norm K : L → K` to the rings of integers.

### Main Results

#### Algebra.coe_norm_int

```lean
theorem Algebra.coe_norm_int {K : Type*} [Field K] [NumberField K] (x : 𝓞 K) :
    (Algebra.norm ℤ x : ℤ) = Algebra.norm ℚ (x : K)
```

The norm over ℤ (as an element of ℤ) equals the norm over ℚ when cast appropriately.

#### Algebra.coe_trace_int

Analogous result for the trace:
```lean
theorem Algebra.coe_trace_int {K : Type*} [Field K] [NumberField K] (x : 𝓞 K) :
    (Algebra.trace ℤ x : ℤ) = Algebra.trace ℚ (x : K)
```

#### RingOfIntegers.coe_norm

```lean
@[simp]
theorem RingOfIntegers.coe_norm (K : Type*) {L : Type*} [Field K] [Field L]
    [Algebra K L] ... (x : 𝓞 L) :
    (RingOfIntegers.norm K x : L) = Algebra.norm K (x : L)
```

Simp rule relating the norm morphism to the algebraic norm.

#### RingOfIntegers.coe_algebraMap_norm

```lean
theorem RingOfIntegers.coe_algebraMap_norm (K : Type*) {L : Type*} ...
    (x : 𝓞 L) :
    (algebraMap (𝓞 K) K (RingOfIntegers.norm K x)) = Algebra.norm K (x : L)
```

#### RingOfIntegers.algebraMap_norm_algebraMap

Compatibility of norm with nested algebraMaps:
```lean
theorem RingOfIntegers.algebraMap_norm_algebraMap ...
```

#### RingOfIntegers.norm_algebraMap

```lean
theorem RingOfIntegers.norm_algebraMap (K : Type*) {L : Type*} ...
    (x : 𝓞 K) :
    RingOfIntegers.norm K (algebraMap (𝓞 K) (𝓞 L) x) =
    x ^ FiniteDimensional.finrank K L
```

The norm of an algebraMap element equals that element raised to the extension degree.

#### RingOfIntegers.dvd_norm

```lean
theorem RingOfIntegers.dvd_norm (K : Type*) {L : Type*} ...
    [IsGalois K L] (x : 𝓞 L) :
    x ∣ algebraMap (𝓞 K) (𝓞 L) (RingOfIntegers.norm K x)
```

In finite Galois extensions, x divides the image of norm K x under algebraMap. This is the key divisibility property used for prime ideal splitting arguments.

#### RingOfIntegers.isUnit_norm_of_isGalois

```lean
theorem RingOfIntegers.isUnit_norm_of_isGalois (K : Type*) {L : Type*} ...
    [IsGalois K L] {x : 𝓞 L} :
    IsUnit (RingOfIntegers.norm K x) ↔ IsUnit x
```

Unit status is preserved by the norm in Galois extensions.

#### RingOfIntegers.isUnit_norm

```lean
theorem RingOfIntegers.isUnit_norm (K : Type*) {L : Type*} ...
    [CharZero K] {x : 𝓞 L} :
    IsUnit (RingOfIntegers.norm K x) ↔ IsUnit x
```

Same result without requiring Galois, just characteristic zero.

#### RingOfIntegers.norm_norm

```lean
theorem RingOfIntegers.norm_norm (K L : Type*) {M : Type*} ...
    (x : 𝓞 M) :
    RingOfIntegers.norm K (RingOfIntegers.norm L x) =
    RingOfIntegers.norm K x
```

Transitivity: the norm through an intermediate field equals the direct norm. More precisely: N_{M/K} = N_{L/K} ∘ N_{M/L}.

### Connection to CM Norm-1 Elements (Erd46 Project)

In `NumberFieldDeep_CM.lean`, the following results are proved:

**norm_div_star_eq_one**: `‖z / star z‖ = 1` for z : ℂ (pure complex analysis)

**cm_norm_div_conj_eq_one**: For α in a CM field K with complex conjugation c: K → K, the element α / c(α) has norm 1 at each complex embedding φ: K → ℂ, i.e., ‖φ(α / c(α))‖ = 1.

**normAtPlace_mixedEmbedding_cm_div_conj_eq_one**: The normAtPlace equals 1 at each complex place for α / c(α).

**mixedEmbedding_cm_div_conj_complex_norm_one**: The concrete ‖.2 w‖ = 1 per complex place w.

These results use:
- `IsCMField.complexConj` — the complex conjugation automorphism of a CM field
- `IsCMField.complexEmbedding_complexConj` — how complex conjugation acts on embeddings
- `RingOfIntegers.isUnit_norm` — to go from norm = 1 to unit properties

### Key Type: 𝓞 K (Ring of Integers)

In Mathlib, `𝓞 K = RingOfIntegers K` is defined as the integral closure of ℤ in K.

```lean
abbrev RingOfIntegers (K : Type*) [Field K] := integralClosure ℤ K
```

The coercion `(x : 𝓞 K) → K` is given by `algebraMap (𝓞 K) K`.

### Ideal Norm vs Field Norm

- `Algebra.norm K : L → K` — the field norm (algebraic norm)
- `Ideal.absNorm : Ideal (𝓞 K) → ℕ` — the ideal norm (index in O_K)

These are related by: for a principal ideal (α) where α ∈ 𝓞 K:
> Ideal.absNorm (ideal.span {α}) = |Algebra.norm ℚ α|

### Source Link

GitHub source:
https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/NumberField/Norm.lean

Mathlib docs (if page exists):
https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/Norm.html
