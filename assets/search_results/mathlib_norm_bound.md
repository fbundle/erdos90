# Source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/CanonicalEmbedding/NormBound.html

## Fetch Result

The URL https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/CanonicalEmbedding/NormBound.html returned HTTP 404 Not Found.

This page may not exist in the current deployed version of Mathlib documentation, or the module path may have changed.

---

## Alternative: Mathlib NumberField Norm-Bound Content

Based on available documentation and the Mathlib source, here is what is known about norm bounds in the canonical embedding context.

### Module: Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormBound

This module (if it exists) likely contains lemmas relating the algebraic norm of number field elements to their Euclidean norm in the mixed embedding / canonical embedding into ℝ^r₁ × ℂ^r₂.

### Key Related Modules (Available via Mathlib docs)

#### Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

Available at: `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/Basic.lean`

Contains:
- `mixedEmbedding K : K →+* ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)` — the canonical mixed embedding
- `integerLattice K : Submodule ℤ (mixedSpace K)` — image of O_K in mixed space
- `latticeBasis K` — a Z-basis for the integer lattice
- `fundamentalDomain_integerLattice` — `IsAddFundamentalDomain (integerLattice K) (ZSpan.fundamentalDomain (latticeBasis K))`
- `volume_fundamentalDomain_latticeBasis` — `volume (fundamentalDomain (latticeBasis K)) = (2)⁻¹^nrComplexPlaces K * sqrt ‖discr K‖₊`

#### Mathlib.NumberTheory.NumberField.ClassNumber

Contains:
- `M K` : Minkowski bound = `(4 / π) ^ nrComplexPlaces K * ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)`
- `classNumber_eq_one_iff` : h(K) = 1 ↔ O_K is a PID
- `exists_ideal_in_class_of_norm_le` : Every ideal class has a representative with norm ≤ M(K)
- `isPrincipalIdealRing_of_isPrincipal_of_norm_le`
- `Rat.classNumber_eq` : h(Q) = 1

### Key Lemmas for Norm Bounds in Mixed Embedding

The canonical embedding φ: K → ℝ^r₁ × ℂ^r₂ sends α to:
- Real coordinates: (σ(α))_{σ : K → ℝ real embeddings}
- Complex coordinates: (σ(α))_{σ : K → ℂ complex embeddings up to conjugation}

For the norm bound, the key formula is:

> |N_{K/Q}(α)| = ∏_{v | ∞} ‖φ_v(α)‖^{nv}

where n_v = 1 for real places and n_v = 2 for complex places.

More precisely in the Minkowski norm: if ‖φ(α)‖_∞ ≤ B (sup-norm bound), then:
> |N_{K/Q}(α)| ≤ B^n   (for sup-norm)
> |N_{K/Q}(α)| ≤ (B/√n)^n  (AM-GM)

### normAtPlace in Mathlib

The function `normAtPlace` in Mathlib:
```lean
def normAtPlace (w : InfinitePlace K) : K → ℝ≥0
```

satisfies:
- For a real place w: `normAtPlace w x = ‖embedding w x‖`
- For a complex place w: `normAtPlace w x = ‖embedding w x‖`

And the norm formula:
```lean
theorem prod_normAtPlace_eq_abs_norm (x : K) :
    ∏ w, normAtPlace w x ^ w.mult = |Algebra.norm ℚ x|
```
where `w.mult = 1` for real places and `w.mult = 2` for complex places.

### For the Erd46 Project

The relevant lemmas for the sorry gaps:

**`hΛ_sep`** (in `gs_tower_levels`): first-coordinate separation for ℤ[I]^f  
Needed: for nonzero v ∈ Λ, ‖v(fin0 hf)‖ ≥ D⁻¹

This requires knowing that the integer lattice in the CM field tower has a specific covolume and minimum vector length. The separation bound comes from:
- The covolume of the integer lattice = (2^(-r₂)) · √|disc(K)| (from `volume_fundamentalDomain_latticeBasis`)
- Minkowski's theorem: the minimum nonzero vector length in a lattice of covolume V in ℝⁿ is ≥ (V/ωₙ)^(1/n)
- For integer lattices in number fields: N_{K/Q}(α) ≥ 1 for nonzero α ∈ O_K, which gives a lower bound on the Euclidean norm

### Module Path Note

The module `Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormBound` may have been:
1. Renamed in a recent Mathlib version
2. Merged into `CanonicalEmbedding.Basic`
3. Not yet added to the docs server

To find the actual content, search for `normBound` in the Mathlib source at:
https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/NumberTheory/NumberField/CanonicalEmbedding/
