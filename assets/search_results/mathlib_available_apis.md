# Mathlib APIs Available for the Two Sorry Gaps

Search date: 2026-05-23. All paths under vendor/mathlib4/Mathlib/.

---

## 0. Chebotarev Density Theorem in Lean4/Mathlib

**Status: ADVANCED DEVELOPMENT (May 2026)**

- **Project**: `PrimeNumberTheoremAnd` (PNT+) led by Terence Tao and Alex Kontorovich.
- **Goal**: Formalizing CDT as a prerequisite for Fermat's Last Theorem (Kevin Buzzard's project).
- **Status**: 
    - Dirichlet's Theorem for Primes in Arithmetic Progressions: **DONE**.
    - Prime Number Theorem (with error term): **DONE**.
    - Full Chebotarev Density Theorem: Most analytic and algebraic lemmas are finished; full merge into Mathlib expected by late 2026.
    - Frobenius elements and Artin symbols are now available in the project's repository.
- **Source**: `https://github.com/AlexKontorovich/PrimeNumberTheoremAnd`

---

## 1. CM Field API (`NumberField/CMField.lean`)

```
IsCMField (K : Type*) [Field K] [CharZero K] : Prop
  -- requires: IsTotallyComplex K, is_quadratic (quadratic over totally real subfield K⁺)

IsCMField.isTotallyComplex : IsTotallyComplex K
IsCMField.complexConj : K ≃ₐ[K⁺] K
  -- the nontrivial automorphism over K⁺ (complex conjugation)

IsCMField.complexEmbedding_complexConj (φ : K →+* ℂ) (x : K) :
    φ (complexConj K x) = conj (φ x)
  -- KEY: complex conjugation becomes complex conjugation in ℂ

IsCMField.infinitePlace_complexConj (w : InfinitePlace K) (x : K) :
    w (complexConj K x) = w x

IsCMField.complexConj_apply_apply (x : K) : complexConj K (complexConj K x) = x
IsCMField.complexConj_eq_self_iff (x : K) : complexConj K x = x ↔ x ∈ K⁺

IsCyclotomicExtension.isCMField {S : Set ℕ} (hS : ∃ n ∈ S, 2 < n) [IsCyclotomicExtension S ℚ K] :
    IsCMField K
  -- cyclotomic extensions with n > 2 are CM
```

### Key Proved Lemmas (Already in erd46 §4)
- `norm_div_star_eq_one : ‖z / star z‖ = 1` for z ≠ 0 in ℂ
- `cm_norm_div_conj_eq_one : ‖φ(α / c(α))‖ = 1` for all embeddings φ
- `normAtPlace_mixedEmbedding_cm_div_conj_eq_one` — per infinite place
- `mixedEmbedding_cm_div_conj_complex_norm_one` — concrete .2 coordinate

---

## 2. Mixed Embedding and Lattice (`CanonicalEmbedding/Basic.lean`)

```
mixedSpace K = ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)
  -- NOT Fin f → ℂ; for totally complex K, no real places, so mixedSpace K = ({...} → ℂ) = {w : IsComplex w} → ℂ

NumberField.mixedEmbedding : K →+* (mixedSpace K)
  -- ring homomorphism

mixedEmbedding_apply_isComplex (x : K) (w : {w // IsComplex w}) :
    (mixedEmbedding K x).2 w = w.val.embedding x

mixedEmbedding_injective [NumberField K] : Function.Injective (mixedEmbedding K)

mixedEmbedding.integerLattice : Submodule ℤ (mixedSpace K)
  -- = Submodule.map (mixedEmbedding K).toLinearMap (Submodule.span ℤ (Set.range (integralBasis K)))

mixedEmbedding.latticeBasis K : Basis (ChooseBasisIndex ℤ (𝓞 K)) ℝ (mixedSpace K)

mixedEmbedding.fundamentalDomain_integerLattice :
    IsAddFundamentalDomain (integerLattice K) (ZSpan.fundamentalDomain (latticeBasis K))

mixedEmbedding.normAtPlace (w : InfinitePlace K) : (mixedSpace K) →*₀ ℝ
normAtPlace_apply_of_isComplex {w : InfinitePlace K} (hw : IsComplex w) (x : mixedSpace K) :
    normAtPlace w x = ‖x.2 ⟨w, hw⟩‖

normAtPlace_apply (w : InfinitePlace K) (x : K) : normAtPlace w (mixedEmbedding K x) = w x
```

### Totally Complex Case
For K with `IsTotallyComplex K`:
- `IsTotallyComplex.nrRealPlaces_eq_zero` : nrRealPlaces K = 0
- `IsTotallyComplex.finrank` : finrank ℚ K = 2 * nrComplexPlaces K
- mixedSpace K first component is empty (no real places)
- So mixedSpace K = ({w : InfinitePlace K // IsComplex w} → ℂ) modulo WithLp
- Need `Fintype.equivFin {w : InfinitePlace K // IsComplex w}` to bridge to `Fin f → ℂ`

---

## 3. Volume and Discriminant (`Discriminant/Basic.lean`)

```
mixedEmbedding.volume_fundamentalDomain_latticeBasis :
    volume (ZSpan.fundamentalDomain (latticeBasis K)) = (2:ℝ≥0∞)⁻¹ ^ nrComplexPlaces K * sqrt ‖discr K‖₊

mixedEmbedding.covolume_integerLattice :
    ZLattice.covolume (integerLattice K) = (2⁻¹) ^ nrComplexPlaces K * √|discr K|
```

---

## 4. Class Number (`ClassNumber.lean`)

```
classNumber K : ℕ = Fintype.card (ClassGroup (𝓞 K))
classNumber_pos : 0 < classNumber K
classNumber_ne_zero : classNumber K ≠ 0

exists_ideal_in_class_of_norm_le (C : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = C ∧ absNorm (I : Ideal (𝓞 K)) ≤ M K
  -- where M K = (4/π)^nrComplexPlaces K * ((finrank ℚ K)! / (finrank ℚ K)^(finrank ℚ K) * √|discr K|)
  -- This is the Minkowski bound — every ideal class contains an ideal of norm ≤ M K
```

**Note**: No explicit bound h(K) ≤ rd(K)^{C·[K:ℚ]} is in Mathlib.
The Minkowski bound M K grows exponentially in finrank ℚ K, but the explicit constant C_class is not formalized.

---

## 5. Totally Real/Complex (`InfinitePlace/TotallyRealComplex.lean`)

```
IsTotallyComplex (K : Type*) [Field K] : Prop
  -- all places are complex

IsTotallyComplex.isComplex : ∀ v : InfinitePlace K, v.IsComplex
IsTotallyComplex.nrRealPlaces_eq_zero : nrRealPlaces K = 0
IsTotallyComplex.finrank : finrank ℚ K = 2 * nrComplexPlaces K
IsTotallyComplex.complexEmbedding_not_isReal (φ : K →+* ℂ) : ¬ ComplexEmbedding.IsReal φ

isTotallyComplex_of_algebra [IsTotallyComplex F] [Algebra F K] ... : IsTotallyComplex K
  -- totally complex is inherited by extensions
```

---

## 6. ZSpan and Fundamental Domain (`Algebra/Module/ZLattice/Basic.lean`)

```
ZSpan.isAddFundamentalDomain (b : Basis ι ℝ E) (μ : Measure E) :
    IsAddFundamentalDomain (span ℤ (Set.range b)) (fundamentalDomain b) μ

ZSpan.isAddFundamentalDomain_toAddSubgroup :
    IsAddFundamentalDomain (span ℤ (Set.range b)).toAddSubgroup (fundamentalDomain b) μ

ZSpan.fundamentalDomain (b : Basis ι ℝ E) : Set E
```

---

## 7. Cyclotomic Fields (`Cyclotomic/Basic.lean`)

```
IsCyclotomicExtension.isCMField {S : Set ℕ} (hS : ∃ n ∈ S, 2 < n) [IsCyclotomicExtension S ℚ K] :
    IsCMField K
IsCyclotomicExtension.isGalois [IsCyclotomicExtension S K L] : IsGalois K L
```

---

## 8. Infinite Galois Theory (`FieldTheory/Galois/Infinite.lean`, `Profinite.lean`)

```
IntermediateFieldEquivClosedSubgroup [IsGalois k K] : (IntermediateField k K)ᵒᵈ ≃o ClosedSubgroup Gal(K/k)
  -- fundamental theorem of infinite Galois theory (Krull topology)

profiniteGalGrp [IsGalois k K] : ProfiniteGrp
  -- Gal(K/k) as a profinite group
continuousMulEquivToLimit [IsGalois k K] : Gal(K/k) ≃* limit (finGaloisGroupFunctor k K)
```

**Note**: API covers infinite Galois theory in general, but no specific pro-p group theory (Golod–Shafarevich, Frattini subgroups, relation rank) is formalized.

---

## 9. What Is Provably Buildable from Existing Mathlib

### For `exists_cm_class_group_data` (Prop 2.2):
Assuming we have a specific CM field K (e.g., cyclotomic) and split primes, we can:
- Prove h(K) is finite: `instFintypeClassGroup` (Fintype (ClassGroup (𝓞 K)))
- Construct the pigeonhole: `exists_fiber_ge_div` (already proved in §3 of NumberFieldDeep)
- Prove |σ(α/c(α))| = 1: all 4 CM lemmas in §4 are proved

We cannot currently (without new Mathlib development):
- Construct a specific CM field K of degree 2f for arbitrary f (the GS tower gives these, but GS is not in Mathlib)
- Find specific split-prime ideal pairs (𝔓_s, c𝔓_s) in K (no split-prime API for CM fields)
- Prove h(K) ≤ H_ℓ^f with explicit H_ℓ (no root-discriminant tower bound in Mathlib)

### For `gs_tower_levels` (Prop 3.6 + type bridge):
We can:
- Use `IsTotallyComplex.finrank` to relate f and nrComplexPlaces K
- Use `fundamentalDomain_integerLattice` for the fundamental domain
- Use `ZSpan.isAddFundamentalDomain` for the lattice

We cannot:
- Construct the pro-3 tower F = F₀ ⊂ F₁ ⊂ ... (requires GS, not in Mathlib)
- Prove the Frobenius split-prime property (Chebotarev not in Mathlib)
- Build the isomorphism `mixedSpace K ≃ Fin f → ℂ` with transport of fundamental domain + separation
