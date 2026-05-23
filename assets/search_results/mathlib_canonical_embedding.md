# Source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/CanonicalEmbedding/Basic.html

# Mathlib Documentation: Canonical Embedding of Number Fields

## Overview

This documentation page covers the canonical embedding theory for number fields in the Lean 4 mathematics library (Mathlib). The canonical embedding maps a number field into a product of complex numbers indexed by its embeddings.

## Core Definitions

**Canonical Embedding**: The primary definition maps `K →+* ((K →+* ℂ) → ℂ)`, sending each element to a vector indexed by complex embeddings. As stated in the documentation, "the canonical embedding of a number field `K` of degree `n` into `ℂ^n`" applies this ring homomorphism structure.

**Key Properties**:
- The embedding is injective for number fields
- The norm relates to the supremum across all embeddings
- The image of integers under this embedding forms a lattice with finite intersection with any closed ball

## Mixed Embedding

The mixed embedding provides an alternative representation using the mixed space `ℝ^r₁ × ℂ^r₂`, where `r₁` and `r₂` represent counts of real and complex infinite places. This separates real embeddings (mapping to ℝ) from complex embeddings (mapping to ℂ).

### Key type: mixedSpace

`mixedSpace K = ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)`

This is NOT the same as `Fin f → ℂ`; for totally complex K, need `Fintype.equivFin` + `LinearEquiv.piCongrLeft` to bridge.

## Supporting Structures

**Lattice Basis**: A `ℂ`-basis of the embedding space that simultaneously forms a `ℤ`-basis of the integer lattice.

**Standard Basis**: An explicit `ℝ`-basis for the mixed space constructed from indicator vectors at each infinite place.

**Norms at Places**: Functions measuring size at individual infinite places, with the algebraic norm defined as the product of these place-specific norms raised to multiplicities.

## Key Theorems

**`fundamentalDomain_integerLattice`** (in `CanonicalEmbedding/Basic.lean`):
`IsAddFundamentalDomain (integerLattice K) (ZSpan.fundamentalDomain (latticeBasis K))`

**`volume_fundamentalDomain_latticeBasis`** (in same file):
`volume (fundamentalDomain (latticeBasis K)) = (2)⁻¹^nrComplexPlaces K * sqrt ‖discr K‖₊`

**`integerLattice K`**: `Submodule ℤ (mixedSpace K)` (not `AddSubgroup`); convert via `Submodule.toAddSubgroup`

## Measure Theory

The documentation confirms that the mixed space carries an invariant Haar measure with no atoms. The fundamental domain of the standard basis has volume 1.
