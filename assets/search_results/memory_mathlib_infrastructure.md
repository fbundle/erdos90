---
name: Mathlib infrastructure for number field tower
description: Specific Mathlib lemmas relevant to the remaining sorry gaps in erd46
type: reference
originSessionId: 15e9ff09-c395-4925-9dd3-d3affcf1131e
---
These Mathlib 4 lemmas are available (as of 2025) and relevant to the remaining sorries:

**Fundamental domain (key — already works):**
- `NumberField.mixedEmbedding.fundamentalDomain_integerLattice` in `CanonicalEmbedding/Basic.lean` — gives `IsAddFundamentalDomain (integerLattice K) (ZSpan.fundamentalDomain (latticeBasis K))`
- `NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis` — gives finite volume formula `(2)⁻¹^nrComplexPlaces K * sqrt ‖discr K‖₊`

**Cyclotomic fields:**
- `discr_prime_pow` in `Cyclotomic/Discriminant.lean` — exact discriminant formula for ℚ(ζ_{p^k})
- `IsCyclotomicExtension.isCMField` in `NumberField/Cyclotomic/Basic.lean` — cyclotomic extensions are CM

**Class groups:**
- `exists_ideal_in_class_of_norm_le` in `ClassNumber.lean` — every ideal class has a representative with norm ≤ Minkowski bound M K

**Type gap (what's missing):**
- `mixedSpace K = ({w // IsReal w} → ℝ) × ({w // IsComplex w} → ℂ)`, not `Fin f → ℂ`
- For a CM field (r₁ = 0): need bijection `{w : InfinitePlace K // IsComplex w} ≃ Fin (nrComplexPlaces K)` via `Fintype.equivFin`, then transport `integerLattice` across `LinearEquiv.piCongrLeft`
- No API for CM split primes → norm-one elements (needed for `prop_2_2`)
