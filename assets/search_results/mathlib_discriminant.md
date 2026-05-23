# Source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/Discriminant/Basic.html

## Module: Mathlib.NumberTheory.NumberField.Discriminant.Basic

### Overview

This Mathlib module defines the discriminant of number fields and proves the two main finiteness theorems.

### Imports

The module imports specialized submodules for:
- Lattices and convex bodies
- Infinite places
- Mixed embeddings

Key imports include:
- `Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic`
- `Mathlib.NumberTheory.NumberField.ClassNumber`
- `Mathlib.MeasureTheory.Measure.Lebesgue`

### Main Theorems

#### 1. Hermite-Minkowski Theorem (`abs_discr_gt_two`)

**Statement:** Any nontrivial number field has discriminant with absolute value strictly greater than 2.

```lean
theorem abs_discr_gt_two (K : Type*) [Field K] [NumberField K] [hn : NeZero (finrank ℚ K)] :
    2 < |discr K|
```

(Exact name and type signature may vary by Mathlib version.)

#### 2. Hermite Theorem (`finite_of_discr_bdd`)

**Statement:** There are only finitely many number fields (in some fixed extension of ℚ) of discriminant bounded by N.

```lean
theorem finite_of_discr_bdd (N : ℤ) :
    Set.Finite {K : Subfield F // NumberField K ∧ |discr K| ≤ N}
```

(Where F is a fixed algebraically closed field of characteristic 0.)

### Key Definitions

#### Root Discriminant (`rootDiscr`)

```lean
noncomputable def rootDiscr (K : Type*) [Field K] [NumberField K] : ℝ :=
    (|discr K| : ℝ) ^ (1 / (finrank ℚ K : ℝ))
```

The nth root of the absolute discriminant, where n = [K:Q]. This is the key invariant for asymptotic number field theory.

#### Minkowski Bound

```lean
noncomputable def M (K : Type*) [Field K] [NumberField K] : ℝ :=
    (4 / π) ^ nrComplexPlaces K *
    ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)
```

### Key Results

#### Covolume and Discriminant

The covolume of the integer lattice in the mixed embedding is related to the discriminant:

```lean
theorem covolume_integerLattice (K : Type*) [Field K] [NumberField K] :
    covolume (integerLattice K) = 2⁻¹ ^ nrComplexPlaces K * √‖discr K‖₊
```

Or equivalently, from `volume_fundamentalDomain_latticeBasis`:
```lean
theorem volume_fundamentalDomain_latticeBasis :
    volume (ZSpan.fundamentalDomain (latticeBasis K)) =
    (2)⁻¹ ^ nrComplexPlaces K * sqrt ‖discr K‖₊
```

#### Discriminant Formula for Cyclotomic Fields

In `Mathlib.NumberTheory.NumberField.Cyclotomic.Discriminant`:

```lean
theorem discr_prime_pow (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [hp : Fact (Nat.Prime p)] (k : ℕ)
    [IsCyclotomicExtension {p ^ k} ℚ K] :
    discr K = ...
```

For K = Q(ζ_{p^k}): disc(K) = ±p^(p^(k-1)(pk-k-1)) (exact formula involves ϕ(p^k) and the prime p).

### Proof Strategy for Hermite Theorem

1. **Bound degree**: Using discriminant bounds, only finitely many degrees n are possible for fields with |disc| ≤ N.

2. **Bound Minkowski norm**: From the Minkowski bound M(K) ≤ C(N), only finitely many Minkowski bounds are possible.

3. **Finite minimal polynomials**: Elements α generating K have conjugates bounded by M(K), so only finitely many minimal polynomials over Q are possible.

4. **Conclude**: There are finitely many possible fields.

Key lemma: `finite_of_finite_generating_set` (used in the proof).

### Odlyzko Bounds (not yet in Mathlib)

The Odlyzko lower bounds on root discriminants are NOT formalized in Mathlib. These are:

For totally real fields: rdiscr(K) ≥ (e^π)^(1+o(1)) ≈ 23.1...
For totally complex fields: rdiscr(K) ≥ (2πe^γ)^(1+o(1)) ≈ 22.3...

These bounds are only known asymptotically and their formalization would require heavy analytic number theory.

### Application to the Erd46 Project

The key formulas used in `NumberFieldDeep_Assembly.lean`:

1. `volume_fundamentalDomain_latticeBasis` — gives covolume of O_K in mixed embedding
2. The Minkowski bound `M K` — bounds h(K) from above
3. `exists_ideal_in_class_of_norm_le` — key step for CM class group data

For the sorry gap in `exists_cm_class_group_data`:
- The card ratio h(K₁)/h(K₂) needs to be bounded
- This uses M(K)/[K:Q] as a bound on h(K)/[K:Q]
- The discriminant formula and Stirling's approximation give M(K) ≤ C^n · √|disc(K)|

### Source Links

GitHub source (likely path):
https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/NumberField/Discriminant/Basic.lean
