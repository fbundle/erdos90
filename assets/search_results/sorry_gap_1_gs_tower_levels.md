# Sorry Gap: `gs_tower_levels` (§2, Prop 3.6 + type bridge)

## Lean Signature

```lean
def gs_tower_levels (ℓ : ℕ) (hℓ : ℓ ≥ 2) (base : GSBaseData ℓ) (M : ℕ) :
    ∃ (f : ℕ), f ≥ M ∧ ∃ (hf1 : f ≥ 1) (Λ : AddSubgroup (Fin f → ℂ))
      (_ : Countable Λ) (F : Set (Fin f → ℂ)),
      IsAddFundamentalDomain Λ F volume ∧ volume F < ∞ ∧
      (∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf1)‖ ≥ base.D₀⁻¹) := by
  sorry
```

Where `base : GSBaseData ℓ` provides `base.D₀ > 0`, `base.rd_F ≥ 1`, `log rd_F ≤ ℓ·log ℓ`.
Currently `gs_base_construction` sets `base.D₀ = 1`, `base.rd_F = 2ℓ`, so `base.D₀⁻¹ = 1`.

---

## What Needs to Be Proved

For any M, produce:
1. **f ≥ M** (large enough field degree)
2. **Λ : AddSubgroup (Fin f → ℂ)** (a discrete lattice in ℂ^f)
3. **Countable Λ** (automatic for discrete lattice)
4. **F : Set (Fin f → ℂ)** (fundamental domain)
5. **IsAddFundamentalDomain Λ F volume** (Λ tiles ℂ^f via F)
6. **volume F < ∞** (F has finite volume)
7. **∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf1)‖ ≥ D₀⁻¹** (first-coordinate separation)

---

## Mathematical Prerequisites

### Step A: Construct the CM field K_j of degree 2f ≥ 2M

**Source**: OpenAI paper §3, Props 3.2–3.6, Prop 3.8

The GS tower construction (Prop 3.8) gives a sequence of totally real fields F_j with f_j = [F_j:ℚ] → ∞ and CM fields K_j = F_j(i). For any M, take j large enough so f_j ≥ M.

**Sub-prerequisites** (all sorry'd in Mathlib):
- Choose ℓ primes r₁,...,rₗ ≡ 1 (mod 3) [primes in APs, Dirichlet — not formalized quantitatively in Mathlib]
- Construct cyclic cubic subfields L_i ⊂ ℚ(ζ_{rᵢ}) [available via IsCyclotomicExtension + Galois theory]
- Form F = cyclic cubic field cut out by χ = χ₁···χₗ [conductor-discriminant formula — not in Mathlib]
- Golod–Shafarevich: G = Gal(F^{ur,3}/F) is infinite when d(G)² > 4r(G) [Prop 3.4 — not in Mathlib]
- Chebotarev: find t = ⌊d²/100⌋ primes q_b with Frobenius in Φ(G) [Prop 3.6 — not in Mathlib]
- Infinite tower from G̅ = G/N [Prop 3.4 applied to G̅ — requires GS, not in Mathlib]

### Step B: Build the lattice Λ ⊂ Fin f → ℂ

**Source**: OpenAI paper §2 (Lattice construction)

Given K_j totally complex of degree 2f, with D₀ = Q² = (∏ q_b)²:

1. Choose f distinct complex embeddings σ_r: K_j → ℂ (one extension of each real embedding of F_j)
2. Define Φ: K_j → ℂ^f by Φ(x) = (σ₁(x),...,σ_f(x))
3. Set Λ = Φ(D₀⁻¹ · 𝒪_{K_j})

In Lean terms, K_j has `IsTotallyComplex K_j` and `[K_j:ℚ] = 2f`, so:
- `nrRealPlaces K_j = 0` (from `IsTotallyComplex.nrRealPlaces_eq_zero`)
- `nrComplexPlaces K_j = f` (from `IsTotallyComplex.finrank : finrank ℚ K_j = 2f`)
- `mixedSpace K_j = (∅ → ℝ) × ({w : IsComplex w} → ℂ)` — purely complex
- `{w : InfinitePlace K_j // w.IsComplex}` has cardinality f

### Step C: Type bridge mixedSpace K_j → Fin f → ℂ

**The gap**: Mathlib's `mixedEmbedding.integerLattice K` lives in `Submodule ℤ (mixedSpace K)`, but the formalization needs `AddSubgroup (Fin f → ℂ)`.

**Proof strategy** (not yet done in Lean):
```lean
-- Step 1: show mixedSpace K_j first component is empty
have h_empty : IsEmpty {w : InfinitePlace K_j // w.IsReal} :=
  Fintype.card_eq_zero_iff.mp (IsTotallyComplex.nrRealPlaces_eq_zero K_j)
-- ⟹ (mixedSpace K_j).1 is ({} → ℝ) ≅ Unit

-- Step 2: equivalence for complex places
let e : {w : InfinitePlace K_j // w.IsComplex} ≃ Fin f :=
  Fintype.equivFin _  -- since nrComplexPlaces K_j = f

-- Step 3: linear isomorphism (mixedSpace K_j).2 ≃ₗ (Fin f → ℂ)
let L : ({w : InfinitePlace K_j // w.IsComplex} → ℂ) ≃ₗ[ℂ] (Fin f → ℂ) :=
  LinearEquiv.piCongrLeft ℂ (fun _ => ℂ) e.symm

-- Step 4: compose with mixedEmbedding.integerLattice K_j
-- to get AddSubgroup (Fin f → ℂ)
let Λ : AddSubgroup (Fin f → ℂ) := (integerLattice K_j).toAddSubgroup.map L.toAddEquiv
```

**Volume transport**: `volume_fundamentalDomain_latticeBasis` and `ZSpan.isAddFundamentalDomain` transport across the LinearEquiv, preserving `IsAddFundamentalDomain` (needs `MeasurePreserving (L.toEquiv)` or `volume_map_equiv`).

**Key Mathlib tools for the bridge**:
- `LinearEquiv.piCongrLeft ℂ (fun _ => ℂ) e.symm` — permutes indices
- `Fintype.equivFin` — gives {w : IsComplex w} ≃ Fin (nrComplexPlaces K)
- `IsAddFundamentalDomain.image` or equivalent — transport fundamental domain
- `MeasureTheory.Measure.map_apply` — volume preservation under linear isomorphisms

### Step D: First-coordinate separation ‖v (fin0 hf1)‖ ≥ D₀⁻¹

**Mathematical content**: For 0 ≠ v ∈ Λ, β = D₀·v = Q²·v is a nonzero element of 𝒪_{K_j}.
Product formula: ∏_{r=1}^f |σ_r(v)| = |N_{K_j/ℚ}(β)|^{1/2} · Q^{-2f} ≥ Q^{-2f} = D₀^{-f}
Since the product of all f coordinates is ≥ D₀^{-f} > 0, at least one coordinate has |σ_r(v)| ≥ D₀⁻¹.

**Gap**: This argument shows SOME coordinate is ≥ D₀⁻¹, not necessarily the FIRST. For the formalization, we need the first coordinate to be ≥ D₀⁻¹.

**Fix**: Re-order the embeddings σ₁,...,σ_f so that σ₁ achieves the maximum, or prove the separation for any specific coordinate by a permutation argument. Alternatively, use a different notion of separation (e.g., sup-norm or max-norm).

**With D₀ = 1** (as in the current sorry): The condition becomes ‖v (fin0 hf1)‖ ≥ 1. For 0 ≠ v ∈ Λ = Φ(𝒪_K), β = v is a nonzero algebraic integer, so ∏|σ_r(β)| = |N_{K/ℚ}(β)|^{1/2} ≥ 1 (norm of nonzero algebraic integer ≥ 1). Still need max ≥ 1 implies first ≥ 1 — only works if we can argue that ALL coordinates ≥ D₀⁻¹... which is false in general.

Actually: with D₀ = 1, D₀⁻¹ = 1. But a lattice vector in ℂ^f can have ‖v₁‖ < 1 with ‖v₂‖ large. So even D₀ = 1 separation in first coordinate requires a non-trivial argument.

**Resolution** (from the paper's Lemma 2.5 proof): The first-coordinate projection π₁: X → ℂ is injective because if σ₁(β) = 0 for a nonzero algebraic integer β ∈ 𝒪_K, that contradicts injectivity of the field embedding σ₁. This means the FIRST COORDINATE IS NEVER ZERO for nonzero lattice vectors — but doesn't give a lower bound on ‖v₁‖.

The lower bound ‖v₁‖ ≥ D₀⁻¹ comes from: for 0 ≠ v ∈ Λ = Φ(D₀⁻¹𝒪_K), D₀·v ∈ 𝒪_K\{0}, so N(D₀·v) ≥ 1, hence ∏|σ_r(D₀v)| ≥ 1, so ∏|σ_r(v)| ≥ D₀^{-f}. The MINIMUM of |σ_r(v)| is ≥ D₀^{-f}/max_{r}|σ_r(v)|^{f-1}... not immediately useful.

**Correct interpretation**: The paper's Lemma 2.6 (size bound) uses the fact that SOME coordinate of λ has modulus ≥ D₀⁻¹ (not necessarily the first). In the Lean formalization, the AdmissibleFamily requires the FIRST coordinate. This is achievable after choosing the labeling of embeddings such that σ₁ achieves the required bound for non-zero lattice vectors.

**Practical approach for the sorry**: The current D₀ = 1 means D₀⁻¹ = 1. For any lattice Λ coming from a number field, the vectors in Λ\{0} satisfy ‖v (fin0)‖ > 0, but not necessarily ≥ 1. This remains a genuine gap even with D₀ = 1.

---

## Available Mathlib APIs for This Sorry

### Can be used directly:
```lean
-- Totally complex finrank
IsTotallyComplex.finrank [NumberField K] [IsTotallyComplex K] :
    finrank ℚ K = 2 * nrComplexPlaces K

-- Zero real places
IsTotallyComplex.nrRealPlaces_eq_zero [NumberField K] [h : IsTotallyComplex K] :
    nrRealPlaces K = 0

-- Fundamental domain (in mixedSpace K)
mixedEmbedding.fundamentalDomain_integerLattice [NumberField K] :
    IsAddFundamentalDomain (integerLattice K) (ZSpan.fundamentalDomain (latticeBasis K))

-- Volume formula
mixedEmbedding.volume_fundamentalDomain_latticeBasis [NumberField K] :
    volume (fundamentalDomain (latticeBasis K)) =
      (2:ℝ≥0∞)⁻¹ ^ nrComplexPlaces K * sqrt ‖discr K‖₊

-- ZLattice tools
ZSpan.isAddFundamentalDomain (b : Basis ι ℝ E) (μ : Measure E) :
    IsAddFundamentalDomain (span ℤ (Set.range b)) (fundamentalDomain b) μ

-- LinearEquiv for piCongrLeft
LinearEquiv.piCongrLeft : (ι ≃ ι') → ((ι → β) ≃ₗ[R] (ι' → β))
Fintype.equivFin : Fintype α → α ≃ Fin (Fintype.card α)

-- Countability
integerLattice is DiscreteTopology → Countable
```

### Missing (requires new Mathlib development):
1. **The CM field K_j itself** — requires GS tower + Chebotarev (not in Mathlib)
2. **Volume transport across LinearEquiv** — `IsAddFundamentalDomain.map_equiv` not in Mathlib in this exact form
3. **First-coordinate separation** — no Lean proof that first coordinate of nonzero lattice vector ≥ D₀⁻¹

---

## Simplest Possible Filling of This Sorry (Stub)

Since D₀ = 1, D₀⁻¹ = 1. The simplest placeholder that is mathematically consistent:

```lean
-- Use ℤ^f as the lattice (integer points in ℂ^f)
-- Λ = image of ℤ^f under the inclusion Fin f → ℂ
-- This satisfies: IsAddFundamentalDomain with the unit cube [0,1)^f
-- volume = 1 < ∞
-- BUT: separation ‖v (fin0)‖ ≥ 1 holds for v ≠ 0 in ℤ^f only if v (fin0) ≠ 0,
--      which is NOT automatic (e.g., v = (0, 1, 0, ..., 0) has v(fin0) = 0)

-- CORRECT stub: Use {v : Fin f → ℂ | ∀ r, ↑(v r).re ∈ ℤ ∧ (v r).im = 0}
-- i.e., the lattice ℤ^f ⊂ Fin f → ℂ (purely real integer points)
-- fundamental domain = [0,1)^f ⊂ ℝ^f ⊂ ℂ^f
-- separation: v ≠ 0 → ∃ r, v r ≠ 0 → ‖v r‖ ≥ 1 (for integers)
--   BUT still doesn't give ‖v (fin0)‖ ≥ 1 since r might not be fin0!

-- WORKAROUND: Pick a lattice where v ≠ 0 → ALL coordinates are nonzero with ‖‖ ≥ 1
-- This exists (e.g., algebraic number field with no embedding = 0 for nonzero element)
-- But hard to construct in Lean without ANT machinery.

-- CONCLUSION: The sorry is genuinely needed for the first-coordinate separation.
```

---

## Summary of Blockers

| Requirement | Available in Mathlib? | Severity |
|-------------|----------------------|---------|
| CM field K_j of degree 2f | No (requires GS tower) | Critical |
| f_j → ∞ from infinite tower | No (requires GS + infinite pro-p groups) | Critical |
| Split primes q_b in K_j | No (requires Chebotarev) | Critical |
| mixedSpace K_j → Fin f → ℂ bridge | Partially (need piCongrLeft + equivFin) | Moderate |
| IsAddFundamentalDomain transport | Not as a standalone lemma | Moderate |
| volume F < ∞ | Yes (from volume formula) | Done |
| Countable Λ | Yes (from DiscreteTopology) | Done |
| First-coordinate separation ‖v(fin0)‖ ≥ D₀⁻¹ | No (requires careful embedding choice) | Critical |

---

## References

- OpenAI paper §3, Props 3.2–3.8 (pages 10-14 of unit-distance-proof.pdf)
- Sawin (arXiv:2605.20579), Lemma 11–12 — explicit GS tower + lattice construction
- Golod–Shafarevich: GS64 = "On the class field tower" (Izv. Akad. Nauk, 1964)
- Shafarevich: Sha63, Sha66 — "Extensions with given points of ramification"
- Neukirch-Schmidt-Wingberg (NSW08): "Cohomology of Number Fields", Ch. X §10
- Koch (Koc02): "Galois Theory of p-Extensions", Ch. 11
- Hajir–Maire–Ramakrishna (HMR21): "Cutting towers of number fields" (Ann. Math. Québec)
- arXiv:2406.00797 — "Infinite class field tower with small root discriminant"
- Mathlib: CanonicalEmbedding/Basic.lean (integerLattice, latticeBasis, fundamentalDomain)
- Mathlib: Discriminant/Basic.lean (volume_fundamentalDomain_latticeBasis)
- Mathlib: InfinitePlace/TotallyRealComplex.lean (IsTotallyComplex, nrComplexPlaces)
