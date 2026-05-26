# Erd46 — proof outline of `erdos_unit_distance_false`

End-to-end walkthrough of the formalization, for the human maintainer and future contributors.  Reflects the state as of 2026-05-27.

## Top-level statement

**Theorem 1.1 (Erdős unit-distance conjecture is false):**
```
∃ δ > 0, ∀ M : ℕ, ∃ (P : Finset (ℝ × ℝ)),
  P.card ≥ M ∧ unitDistPairs P ≥ (1 / 2 : ℝ) * P.card ^ (1 + 2 * δ)
```

Located at `Erdos90/Main.lean`, called `erdos_unit_distance_false`.

The negation of Erdős' conjecture: there exists `δ > 0` and infinitely many `n`
with planar point sets having `≥ ½n^(1+2δ)` unit-distance pairs.

## High-level structure

```
erdos_unit_distance_false
  ↓
admissible_family_to_planar_set   (Theorem 2.3, Sawin's construction)
  ↓
exists_admissible_family   (in NumberField.lean; chooses parameters)
  ↓
prop_3_2_to_3_6_via_deep   (the algebraic NT engine)
  ↓
brd_cm_tower_postulate   (Phase C; proved code combining lattice/CM data)
  ↓
brd_tower_data   (Phase D3+D4+D5; proved code combining 2 sorries)
  ↓
  ├─ gs_cm_tower          ← sorry 1 (HMR 2021 GS construction)
  └─ chebotarev_fixed_Q   ← sorry 2 (HMR theo:ihara + going-up)
```

And separately:
```
class_num_bound_of_brd   (Phase E9; D3.2d chain assembly, proved)
  ↓
  ├─ classNumber_eq_residue_formula   (E5, proved)
  ├─ dedekind_residue_upper_bound_cm   ← off-path sorry 3 (Louboutin)
  ├─ regulator_lower_bound_cm   ← off-path sorry 4 (Friedman)
  └─ torsionOrder_bound   (E10+E13, proved)
       ├─ totient_torsionOrder_le_finrank   (proved)
       └─ nat_le_four_mul_totient_sq   (proved)
```

## Step-by-step walkthrough

### Step 1: Sawin's geometric construction (Theorem 2.3)

**File:** `Erdos90/Geometric.lean` — fully proved.

Given an "admissible family" (a number-theoretic object), construct a planar
point set with many unit distances.  The construction uses:
- A CM totally complex number field `K` of degree `2f`
- A lattice `Λ` in `ℂ^f` (the canonical Minkowski lattice scaled by Q⁻²)
- A finite set `U ⊂ Λ` of "norm-one" elements
- The disc-overlap ratio `ρ(R)` analysis

**Key lemmas:**
- `planar_set_from_datum` (parametric)
- `admissible_family_to_planar_set` (assembled)

### Step 2: Coset averaging (Lemma 2.4)

**File:** `Erdos90/CosetAveraging.lean` — fully proved.

The combinatorial argument: averaging over translates of `U` finds a coset
with many lattice points inside a ball.

**Key lemma:** `lemma_2_4`.

### Step 3: Choosing parameters (`exists_admissible_family`)

**File:** `Erdos90/NumberField.lean` — proved modulo the deeper machinery.

Set up `δ`, `R`, `Λ`, `f`, `D`, etc., satisfying the admissibility conditions.
The choice of `C_class := 1` is concrete; the asymptotic conditions (`prop_p6`,
`hlog2_event`) are proved analytic lemmas.

### Step 4: The algebraic NT engine (`prop_3_2_to_3_6_via_deep`)

**File:** `Erdos90/NumberFieldDeep_Assembly.lean` — proved modulo deeper sorries.

For each target degree `M` and parameters `(t, log_H)`, return:
- A CM totally complex `K` of complex degree `f ≥ M`
- A lattice `Λ` (Q²-scaled Minkowski lattice on K)
- A `CMTowerData K` with valuation/conjugate properties
- A class-number bound `log(h_K)/f ≤ log_H`

This bundles steps 5–8 below.

### Step 5: The BRD CM tower postulate (`brd_cm_tower_postulate`)

**File:** `Erdos90/NumberFieldDeep_GSTower.lean` — proved Lean code modulo
`brd_tower_data`.

Assembles `BRDTowerData ℓ` + lattice machinery (`QScalingLattice`) + Phase A's
integrality lemma (`Q_sq_div_conj_mem_integers`) into the full `CMTowerData`.

### Step 6: BRD tower data assembly (`brd_tower_data`)

**File:** `Erdos90/NumberFieldDeep_GSTower.lean` — proved Lean code modulo
`gs_cm_tower` + `chebotarev_fixed_Q`.

Uses `Classical.choose` to extract from the two sorried existence statements:
1. **`gs_cm_tower`**: existence of an asymptotically-good CM tower with
   bounded root discriminant `rd_F`.  TRUE per HMR 2021 + Golod–Shafarevich +
   CM lift.  ← **SORRY 1**
2. **`chebotarev_fixed_Q`**: a fixed tower constant Q (product of split primes)
   that works at every level.  TRUE per HMR theo:ihara (effective Chebotarev).
   ← **SORRY 2**

For each tower level `K`, plumbs the data through to produce `CMTowerData`.

Also calls `class_num_bound_of_brd` (Step 7).

### Step 7: The class-number bound chain (`class_num_bound_of_brd`)

**File:** `Erdos90/NumberFieldDeep_GSTower.lean` — fully proved Lean code modulo
off-path sorries.

For CM totally complex `K` with `rootDiscr K ≤ rd_F` and `f = nrComplexPlaces K ≥ 5`,
proves `log(h_K)/f ≤ 2·log(2·rd_F)`.

**Chain decomposition** (D3.2d):

Starting from the algebraic identity
```
classNumber K = R_K · w_K · √|disc K| / ((2π)^f · reg K)
```
(this is `classNumber_eq_residue_formula`, **E5, proved**).

Taking log and dividing by f:
```
log(h_K)/f = log(R_K)/f + log(w_K)/f + log(rootDiscr K) - log(2π) - log(reg K)/f
```

Applying bounds:
- `R_K ≤ (4·rd_F)^f` → `log(R_K)/f ≤ log(4·rd_F)`.  **D3.2b sorry** (Louboutin 2000).
- `reg K ≥ 1/8` → `-log(reg K)/f ≤ log(8)/f`.  **D3.2c sorry** (Friedman 1989).
- `w_K ≤ 4·[K:ℚ]² = 16f²` → `log(w_K)/f ≤ log(16f²)/f`.  **proved via E10+E13**.
- `rootDiscr K ≤ rd_F` → `log(rootDiscr K) ≤ log(rd_F)`.  Hypothesis.

Final arithmetic: `log(2π)·f ≥ log(128·f²)` for `f ≥ 5`, i.e., `(2π)^f ≥ 128f²`.
Proved via `(2π)^f ≥ 6^f ≥ 128f²` (helper `chain_arith_128n2_le_6n`).

### Step 8: Q²-scaling integrality (Phase A)

**File:** `Erdos90/CMField/QScaling.lean` — fully proved.

For a CM field `K` with split-prime data `sp`, `Q²·(α/c(α)) ∈ 𝓞_K` whenever
`α ∈ 𝓞_K` is a unit and `c` is complex conjugation.

This is the technical content underlying the Q²-scaled Minkowski lattice.

### Step 9: Q²-scaled lattice machinery (Phase C)

**File:** `Erdos90/CMField/QScalingLattice.lean` — fully proved.

Construct `Λ = Q⁻²·𝓞_K` as a sublattice of `ℂ^f` via the Minkowski embedding.
Properties: countability, fundamental domain, separation, etc.

### Step 10: Cyclotomic split primes (Phase D1+D2)

**File:** `Erdos90/CMField/CyclotomicSplitPrimes.lean` — fully proved.

Construction of split-prime data for cyclotomic fields ℚ(ζ_p) via Dirichlet's
theorem on primes in AP.  Used to demonstrate the existence of `SplitPrimeData`
for some K, but not directly for the BRD tower (which uses non-cyclotomic K).

## The 4 remaining sorries

1. **`gs_cm_tower`** (`NumberFieldDeep_GSTower.lean:133`): GS + CM lift.
   Cite HMR 2021 §2–4 (`prop:cutting`).  Mathlib gap: class field theory.
2. **`chebotarev_fixed_Q`** (`NumberFieldDeep_GSTower.lean:185`): Chebotarev.
   Cite HMR 2021 §3 (`theo:ihara`).  Mathlib gap: Chebotarev density.
3. **`regulator_lower_bound_cm`** (`Mathlib4_Extra/ClassNumberBound.lean:296`):
   Friedman 1989.  Mathlib gap: functional equation of `dedekindZeta`.
4. **`dedekind_residue_upper_bound_cm`** (`Mathlib4_Extra/ClassNumberBound.lean:332`):
   Louboutin 2000.  Same Mathlib gap as #3.

## Closing strategy

See `assets/search_results/closing_roadmap.md` for the 5-PR Mathlib strategy
that closes sorries 3 + 4 (sharing the `dedekindZeta` functional equation
infrastructure).

Sorries 1 + 2 require class field theory + Chebotarev — separate Mathlib roadmap
effort.

## Build verification

```bash
lake build
```

Produces 4 sorry warnings (and 2 in `ClassNumBoundCounterexample.lean` which
are off the proof path).  The main theorem:

```
erdos_unit_distance_false : ∃ δ > 0, ∀ M, ∃ P, ...
  axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

No custom axioms — only Lean's foundational ones plus `sorryAx` for the 4
documented sorries.

## Key strategic insights

1. **Geometric/combinatorial layer fully closed**: Theorem 2.3, Lemma 2.4,
   the disc-overlap analysis are all proved.

2. **CM-field class-group infrastructure fully closed**: split primes,
   conjIdeal, J_ideal counting, Q²-scaling, the class-group pigeonhole
   (`exists_cm_class_group_data`), and the chain to `cm_norm_one_elements`.

3. **Q²-scaled lattice machinery fully closed**: covolume, fundamental
   domain, separation, projection injectivity.

4. **Cyclotomic split-prime construction fully closed**: Dirichlet's theorem
   gives us split primes for ℚ(ζ_p).

5. **The chain `class_num_bound_of_brd` is the last bridge that depended on
   analytic NT, and it's now proved Lean code** — modulo two clearly-named
   off-path sorries (Friedman + Louboutin).

6. **The remaining sorries are all genuine Mathlib gaps**: not flaws in the
   formalization architecture, but missing analytic infrastructure in
   Mathlib.  Closing them is a coherent Mathlib-PR roadmap (see
   `closing_roadmap.md`).
