# Mathlib v4.29.1 — Cyclotomic Field Instances for CM Field of Degree 2f

Source: vendor/mathlib4/Mathlib/NumberTheory/NumberField/Cyclotomic/Embeddings.lean
        vendor/mathlib4/Mathlib/NumberTheory/NumberField/CMField.lean
        vendor/mathlib4/Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean

---

## Key Theorems Available

### `IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero`
File: Cyclotomic/Embeddings.lean line 33
```lean
theorem nrRealPlaces_eq_zero [IsCyclotomicExtension {n} ℚ K] (hn : 2 < n) :
    nrRealPlaces K = 0
```
Proves totally complex for cyclotomic extensions with n > 2.

### `IsCyclotomicExtension.Rat.isTotallyComplex`
File: Cyclotomic/Embeddings.lean line 39
```lean
theorem isTotallyComplex [IsCyclotomicExtension {n} ℚ K] (hn : 2 < n) :
    IsTotallyComplex K
```

### `IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two`
File: Cyclotomic/Embeddings.lean line 48
```lean
theorem nrComplexPlaces_eq_totient_div_two [IsCyclotomicExtension {n} ℚ K] :
    nrComplexPlaces K = φ n / 2
```
So: for K = ℚ(ζ_{p^k}), nrComplexPlaces K = φ(p^k)/2 = p^{k-1}(p−1)/2.

### `IsCyclotomicExtension.finrank`
File: Cyclotomic/PrimitiveRoots.lean line 43
```lean
theorem finrank [NeZero n] [IsCyclotomicExtension {n} ℚ K]
    (hirr : Irreducible (Polynomial.cyclotomic n K)) :
    Module.finrank ℚ K = n.totient
```

### `IsCyclotomicExtension.Rat.isCMField`
File: CMField.lean line 569
```lean
theorem isCMField {S : Set ℕ} (hS : ∃ n ∈ S, 2 < n)
    [IsCyclotomicExtension S ℚ K] : IsCMField K
```

---

## Constructing CM Field of Degree Exactly 2f

To get a CM field K with `Module.finrank ℚ K = 2f` (i.e., `nrComplexPlaces K = f`):

**Strategy**: Find n with φ(n) = 2f.
- For f = 1: n = 3 gives φ(3) = 2. Use K = CyclotomicField 3 ℚ.
- For f = 2: n = 5 gives φ(5) = 4. Use K = CyclotomicField 5 ℚ.
- For f prime: n = 2f+1 if prime (Sophie Germain primes). Not guaranteed.
- For general f: use n = 2·(2f) if φ(n) = φ(2)·φ(2f) = 2f when 2f+1 is odd squarefree... complicated.

**Cleanest general route** (using Bertrand's postulate):
- By Bertrand, ∃ prime p with 2f < p ≤ 4f.
- Then φ(p) = p-1 ≥ 2f, so the cyclotomic field ℚ(ζ_p) has degree p-1 ≥ 2f.
- This gives a CM field of degree ≥ 2f, NOT exactly 2f.
- For exactly 2f, need p-1 = 2f (i.e., p = 2f+1 prime), not always available.

**For the formalization**: Using a cyclotomic field of degree ≥ 2f would require
changing the type of Λ from `Fin f → ℂ` to `Fin (p-1) → ℂ` (or finding a sub-lattice
of dimension 2f), which requires additional work. The GS tower approach in the paper is
more direct but unavailable.

---

## mixedEmbedding_injective — AVAILABLE

File: vendor/mathlib4/Mathlib/NumberTheory/NumberField/CanonicalEmbedding/Basic.lean
```lean
theorem NumberField.mixedEmbedding_injective (K : Type*) [Field K] [NumberField K] :
    Function.Injective (NumberField.mixedEmbedding K)
```
This is the KEY lemma for hΛ_inj: v = Φ(a) and Φ(a)(fin0) = 0 implies a = 0.
Combined with `mem_cmMinkowskiLattice_iff`, gives hΛ_inj for cmMinkowskiLattice
directly:
```lean
-- Proof sketch (given CM field K exists):
intro v hv hv0
rcases (mem_cmMinkowskiLattice_iff K f hf v).mp hv with ⟨a, ha⟩
have ha0 : a ≠ 0 := fun h => hv0 (by simp [h, map_zero] at ha; exact ha.symm)
-- v(fin0) = (cmMinkowskiEquiv K f hf (mixedEmbedding K a))(fin0)
-- = (mixedEmbedding K a).2 w₀  (by cmMinkowskiEquiv_apply_complex)
-- = InfinitePlace.embedding w₀.val (a : K)  (by mixedEmbedding definition)
-- Since embedding w₀.val : K →+* ℂ is injective (field embedding):
-- v(fin0) = 0 → embedding w₀.val a = 0 → a = 0 → v = 0
```
**Status**: Structurally provable once a CM field K is available; the
`mixedEmbedding_injective` lemma is in Mathlib.

---

## Type Bridge Status (mixedSpace → Fin f → ℂ)

The bridge is **fully working** in our project already:

```lean
-- NumberFieldDeep_CM.lean line 138
noncomputable def prod_left_isEmpty_equiv_snd (ι : Type*) [IsEmpty ι] (V : Type*) [AddCommMonoid V] [Module ℝ V] :
    ((ι → ℝ) × V) ≃ₗ[ℝ] V

-- line 149
noncomputable def mixedSpace_equiv_complex_places (hReal : nrRealPlaces K = 0) :
    mixedEmbedding.mixedSpace K ≃ₗ[ℝ] ({w : InfinitePlace K // IsComplex w} → ℂ)

-- line 162
noncomputable def mixedSpace_equiv_pi_fin_of_card (hReal : nrRealPlaces K = 0) (f : ℕ)
    (hf : InfinitePlace.nrComplexPlaces K = f) :
    mixedEmbedding.mixedSpace K ≃ₗ[ℝ] (Fin f → ℂ)
```

No additional Mathlib API needed for the bridge.

---

## What is Missing in Mathlib (Summary)

| Feature | Status |
|---|---|
| `IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two` | **AVAILABLE** |
| `IsCyclotomicExtension.Rat.isCMField` | **AVAILABLE** |
| `IsCyclotomicExtension.finrank` | **AVAILABLE** (with irreducibility hypothesis) |
| `NumberField.mixedEmbedding_injective` | **AVAILABLE** |
| `ClassGroup.mk0_surjective` | **AVAILABLE** |
| `NumberField.exists_ideal_in_class_of_norm_le` | **AVAILABLE** |
| `IsCMField.complexConj_eq_self_iff` | **AVAILABLE** |
| **Golod-Shafarevich pro-p group tower** | **MISSING** |
| **Chebotarev density theorem** | **MISSING** |
| CM field K of degree exactly 2f for all f | **MISSING** (cyclotomic works for many f, not all) |
| Split-prime predicate `IsSplit` / `IsTotallySplit` | **MISSING** |
| `Ideal.relNorm_of_prime_factor` (N_{K/F}(𝔓) = 𝔭) | **MISSING** |
| Principal generator extraction from ClassGroup fiber | **MISSING** |
| Valuation parity / sign-vector ideal recovery | **MISSING** |
| Relative class number `h⁻(K)` | **MISSING** |
