# Mathlib PR candidates from Erd46

Lemmas in `Erdos90/Mathlib4_Extra/` and elsewhere that are general-purpose and
could be contributed back to Mathlib.  Listed in approximate priority order.

## Definitely Mathlib-PR-shaped (proved here, fits Mathlib organization)

### `Nat.le_four_mul_totient_sq` — reverse totient inequality
**Statement:** `∀ n : ℕ, n ≤ 4 · φ(n)²`

**Local location:** `Erdos90/Mathlib4_Extra/ClassNumberBound.lean`
(`nat_le_four_mul_totient_sq`)

**Proposed Mathlib location:** `Mathlib/Data/Nat/Totient.lean`, alongside
`Nat.totient_le n : φ(n) ≤ n` (line 61).

**Proof sketch:**
- For n ≤ 16: `interval_cases + decide`.
- For n ≥ 17: decompose `n = 2^a · m` via `padicValNat 2 n`, then apply the
  odd helper `odd_le_totient_sq m hm`.
- Odd helper: `∀ m odd, m ≤ φ(m)²`.  Via `Nat.recOnPosPrimePosCoprime`:
  - prime_pow case: split on k=1 vs k≥2 for odd prime p ≥ 3.
  - coprime case: multiplicativity via `Nat.totient_mul`.

**Lines:** ~75.

### `NumberField.classNumber_eq_residue_formula` — algebraic class number formula
**Statement:** `(classNumber K : ℝ) = dedekindZeta_residue K · (torsionOrder K · √|discr K|) / (2^r₁ · (2π)^r₂ · regulator K)`

**Local location:** `Erdos90/Mathlib4_Extra/ClassNumberBound.lean`
(`classNumber_eq_residue_formula`)

**Proposed Mathlib location:** `Mathlib/NumberTheory/NumberField/DedekindZeta.lean`,
alongside `tendsto_sub_one_mul_dedekindZeta_nhdsGT`.

**Proof:** purely algebraic rearrangement of Mathlib's `dedekindZeta_residue_def`.
No analytic content (Mathlib already has the analytic class number formula in
limit form).

**Lines:** ~15.

### `NumberField.Units.totient_torsionOrder_le_finrank`
**Statement:** `(NumberField.Units.torsionOrder K).totient ≤ Module.finrank ℚ K`

**Local location:** `Erdos90/Mathlib4_Extra/ClassNumberBound.lean`
(`totient_torsionOrder_le_finrank`)

**Proposed Mathlib location:** `Mathlib/NumberTheory/NumberField/Units/Basic.lean`
or `Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean`.

**Proof sketch:** Get a primitive `torsionOrder K`-th root of unity in K via
`IsCyclic.exists_ofOrder_eq_natCard` + `IsPrimitiveRoot.iff_orderOf` +
`map_of_injective`.  Apply `IsPrimitiveRoot.lcm_totient_le_finrank` with
`p = q = torsionOrder K` and `Nat.lcm_self`.

**Lines:** ~25.

### `NumberField.Units.torsionOrder_le_finrank_pow_two`
**Statement:** `NumberField.Units.torsionOrder K ≤ 4 · (Module.finrank ℚ K)^2`

**Local location:** `Erdos90/Mathlib4_Extra/ClassNumberBound.lean`
(`torsionOrder_bound`)

**Proposed Mathlib location:** alongside the previous lemma.

**Proof:** Combine the two lemmas above.

**Lines:** ~7.

## Algebraic identity helpers

### `Ideal.absNorm_mem` chain helpers
The proof of `card_ideals_of_norm_le_bound` in our codebase uses:
- `Ideal.absNorm_mem` (already Mathlib)
- `Ideal.absNorm_span_natCast` (already Mathlib)
- `RingOfIntegers.rank` (already Mathlib)
- `Ideal.comap_map_mk` (already Mathlib)
- `Submodule.cardQuot_apply` (already Mathlib)

The lemma itself (crude `|{I : norm ≤ N}| ≤ 2^((N!)^[K:ℚ])` bound) is a
loose-constant variant of the analytic ideal count `O(N)`.  Not directly
Mathlib-shaped; would need the tight `O(N)` version.

## Documented Mathlib gaps (not yet PR-shaped here, but identified)

These are NOT currently proved in this codebase but are clean Mathlib targets
that would unblock our sorries:

### Multi-dimensional Poisson summation
For `f : 𝓢(EuclideanSpace ℝ ι, ℂ)` and a ZLattice `L`,
```
Σ_{x ∈ L} f x = (1 / covolume L) · Σ_{ξ ∈ L^*} fourierIntegral f ξ
```
Where `L^*` is the dual lattice.

Mathlib currently has the 1-D version (`SchwartzMap.tsum_eq_tsum_fourier`).

### Theta function for number-field lattice
```lean
noncomputable def numberFieldTheta (K : Type*) [NumberField K] (t : ℝ) : ℂ :=
  ∑' a : 𝓞 K, Complex.exp (-π * t * ‖(mixedEmbedding K a : mixedSpace K)‖²)
```
With modular transformation via multi-D Poisson summation.

### Functional equation for `dedekindZeta`
Use the theta function + `Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean`'s
WeakFEPair framework to get
```
completedDedekindZeta K (1 - s) = completedDedekindZeta K s
```

See `assets/search_results/closing_roadmap.md` for the full strategy.

## Bottom line

The 3 named lemmas above (totient inequality, algebraic class number formula,
torsionOrder bridge) are all CLEAN Mathlib PRs that can be extracted from
this codebase without depending on the bigger Mathlib gaps.

A motivated contributor could submit these as standalone PRs to Mathlib
v5+, slightly cleaned up.
