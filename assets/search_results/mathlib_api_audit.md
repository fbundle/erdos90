# Mathlib API Audit (v4.30)

## 1. Number Field Basics

- **`NumberField.classNumber`**
  - Path: `Mathlib/NumberTheory/NumberField/ClassNumber.lean`
  - Signature: `noncomputable def classNumber : ℕ`
  - Definition: `Fintype.card (ClassGroup (𝓞 K))`
  - Lemmas: `classNumber_ne_zero`, `classNumber_pos`, `classNumber_eq_one_iff`.

- **`NumberField.discr`**
  - Path: `Mathlib/NumberTheory/NumberField/Discriminant/Defs.lean`
  - Signature: `noncomputable abbrev discr : ℤ`
  - Definition: `Algebra.discr ℤ (RingOfIntegers.basis K)`
  - Note: This is the absolute discriminant of the number field.

## 2. Canonical and Mixed Embeddings

- **`NumberField.mixedEmbedding`**
  - Path: `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/Basic.lean`
  - Signature: `noncomputable def mixedEmbedding : K →+* (mixedSpace K)`
  - Components: Real parts for real places, complex parts for complex places.

- **`mixedEmbedding.integerLattice`**
  - Path: `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/Basic.lean`
  - Signature: `def integerLattice : Submodule ℤ (mixedSpace K)`
  - Note: Image of $\mathcal{O}_K$ under the mixed embedding.

- **`mixedEmbedding.latticeBasis`**
  - Path: `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/Basic.lean`
  - Signature: `noncomputable def latticeBasis : Basis (ChooseBasisIndex ℤ (𝓞 K)) ℝ (mixedSpace K)`

- **Fundamental Domain**
  - Path: `Mathlib/Algebra/Module/ZLattice/Basic.lean`
  - Signature: `ZSpan.fundamentalDomain (b : Basis ι ℝ V)`
  - Lemma: `ZSpan.isAddFundamentalDomain basis volume`

- **Infinite Places**
  - `InfinitePlace.nrRealPlaces K`
  - `InfinitePlace.nrComplexPlaces K`
  - `InfinitePlace.isReal`, `InfinitePlace.isComplex`

## 3. CM Fields

- **`IsCMField`**
  - Path: `Mathlib/NumberTheory/NumberField/Basic.lean` (or `NumberField/Cyclotomic/Basic.lean`)
  - Definition: Number field $K$ with a totally real subfield $F$ such that $K/F$ is a totally complex quadratic extension.
  - API: `IsCMField.complexConj`, `IsCMField.complexEmbedding_complexConj`.

- **Cyclotomic Fields**
  - `IsCyclotomicExtension {p} ℚ K`
  - `IsCyclotomicExtension.Rat.isCMField`
