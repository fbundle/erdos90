# CLAUDE.md — Instructions for continuing this Lean 4 formalization

## What this project is

A Lean 4 formalization of Theorem 1.1 from the OpenAI paper *"Planar Point Sets with Many Unit Distances"* (2026).  The theorem disproves the Erdős unit-distance conjecture:

> ∃ δ > 0 such that ν(n) ≥ n^{1+δ} for infinitely many n.

Here ν(n) = maximum number of unit-distance pairs among n points in the plane.

## File structure

| File | Purpose |
|------|---------|
| `Erdos90/Defs.lean` | Core definitions: `distSq`, `unitDistPairs`, `maxUnitDists` |
| `Erdos90/Arithmetic.lean` | `AdmissibleFamily` structure + Axiom 1 (tower existence) |
| `Erdos90/Geometric.lean` | Axioms 2–5, `GoodCoset`, Theorems 2.3a/b (planar set from family) |
| `Erdos90/Main.lean` | Theorem 1.1 (`erdos_unit_distance_false`) + contrapositive |
| `Erdos90/Axioms.lean` | Human-readable index of all 5 axioms with mathematical context |
| `Erdos90.lean` | Root import (imports all modules) |
| `lakefile.toml` | Build configuration (mathlib dependency, library target `Erd46`) |

## Rules

**Read `README.md` before doing anything.**  It contains project constraints and conventions set by the human maintainer.  Do not duplicate its content here — read it directly.

In particular: never edit or commit `README.md` itself.

## Build

```bash
lake build
```

Requires `leanprover/lean4:v4.29.1` and mathlib (declared in `lakefile.toml`).  The build succeeds — remaining gaps are `sorry` warnings, not compilation errors.

## The 5 axioms

These are statements assumed without proof, corresponding to deep theorems in the literature.  They are declared in the source files and documented together in `Axioms.lean`.

1. **`exists_admissible_family`** (`Arithmetic.lean`) — Golod-Shafarevich tower: ∃ γ>0, D>0, ∀ large M, ∃ A with A.f ≥ M, A.γ = γ, A.D = D

2. **`exists_R_log_rho_gt`** (`Geometric.lean`) — disc-overlap ratio ρ(R) → 1: ∀ ε>0, D>0, ∃ R>½, log ρ(R) > -ε ∧ 4RD > 1

3. **`exists_good_coset`** (`Geometric.lean`, `def` not `lemma` — returns `GoodCoset` structure) — Haar measure coset averaging

4. **`size_bound`** (`Geometric.lean`) — sup-norm packing: |X| ≤ exp(2f·log(4RD))

5. **`first_coordinate_separation`** (`Geometric.lean`) — for nonzero v ∈ Λ, ‖v(fin0 A.hf)‖ ≥ D⁻¹

## Current proof state (what's done, what's `sorry`)

### Done (proven in Lean)
- `projection_injective` — first-coordinate projection injective on a Λ-coset (Lemma 2.5)
- `card_ordered_unit_pairs_eq_two_mul_unitDistPairs` — swap involution + strong induction (cardinality even)
- `distSq_symm` — symmetry of Euclidean distance
- `unitDistPairs_le_maxUnitDists` — any finite planar set achieves ≤ maxUnitDists (`Main.lean`)
- **`h_card_le`** (inside both `planar_set_from_datum` and `admissible_family_to_planar_set`) — injection φ(x,y) = (re_im(π₁ x), re_im(π₁ y)) from U-pairs into ordered unit-distance pairs; key: `‖z‖^2 = normSq z` via `simp [Complex.norm_def, Real.sq_sqrt (normSq_nonneg _)]`
- **`h_P_lower`** (inside `planar_set_from_datum`) — |P| ≥ exp(γ/2·f), proved from E ≤ N² and E ≥ exp·N
- **`h_exp_bound`** (inside both theorems) — exp(γ/2·f) ≥ |P|^{2δ} via `Real.rpow_def_of_pos` + log monotonicity
- **rpow identity** — (P.card)^(2δ)·P.card = (P.card)^(1+2δ), via `Real.rpow_add` + `Real.rpow_one`
- **`erdos_unit_distance_false`** (Theorem 1.1, `Main.lean`) — fully proven
- **`erdos_bound_false`** (contrapositive, `Main.lean`) — fully proven

### Deep axioms (`sorry` — awaiting human verification)
- `exists_good_coset` (Axiom 3) — Haar measure averaging on the torus ℂ^f/Λ
- `size_bound` (Axiom 4) — sup-norm packing: |X| ≤ exp(2f·log(4RD))

These are the only remaining `sorry` gaps in the project.

## Important types and notations

- `AdmissibleFamily` has fields: `f`, `hf`, `D`, `hD`, `γ`, `hγ`, `Λ` (AddSubgroup), `U` (Finset), `hU_mod`, `hU_in_Λ`, `hU_size`, `hΛ_sep`
- `fin0 hf` is the first element of `Fin f` (guards f ≥ 1)
- `polydisc f R` is the sup-norm polydisc in ℂ^f
- `shift a S` is translation of set S by vector a
- `distSq` is squared Euclidean distance on ℝ×ℝ
- `unitDistPairs P` counts *unordered* unit-distance pairs (filtered offDiag / 2)
- `GoodCoset A R` packages the coset averaging result
- `rho R` is the disc-overlap ratio a(R)/b(R)
- `planar_set_from_datum A R hR hρ h_4RD` — parametric form of Theorem 2.3; outputs |P| ≥ 1, |P| ≥ exp(γ/2·f), |P| ≤ exp(B·f), and ν(P) ≥ ½·exp·|P|
- `admissible_family_to_planar_set A` — corollary that picks R internally and outputs ν(P) ≥ ½·|P|^{1+2δ}

## Key Mathlib API facts (non-obvious)

- `‖z‖^2 = normSq z` for `z : ℂ`: use `simp [Complex.norm_def, Real.sq_sqrt (normSq_nonneg _)]` — **`Complex.abs`, `Complex.abs_apply`, `Complex.norm_eq_abs` do NOT exist** in this Mathlib version
- `Real.rpow_def_of_pos hx (e) : x^e = exp(log x * e)` — note multiplication order (log x * e, not e * log x)
- `Real.rpow_le_rpow_left_iff (h : 1 < b) : b^x ≤ b^y ↔ x ≤ y`
- `one_lt_exp_iff.mpr hx : exp x > 1` when `x > 0` — **`Real.one_lt_exp` does NOT exist**
- `Nat.le_ceil x : x ≤ ⌈x⌉₊` (for ceiling)
- Local `let` bindings are NOT unfolded by `simp only` or `dsimp only` — use `.mp` / `.mpr` directly

## Tips for continuing

1. **Don't touch README.md.**  Ever.

2. The `swap` involution proof for even cardinality used `Finset.strongInductionOn` with a generalized induction hypothesis (`revert` trick).  This pattern works for similar combinatorial arguments.

3. For `erdos_unit_distance_false`: choose M = max(⌈log N / (γ/2)⌉₊, ⌈log 2 / (γ/2·δ)⌉₊), get A from the tower with A.f ≥ M, then rewrite A.γ = γ and A.D = D before calling `planar_set_from_datum`. Use `Real.log_lt_log` for monotonicity. The `Nat.cast_le.mp` typeclass can get stuck — use `have h : (N : ℝ) ≤ (P.card : ℝ) := ?_; exact_mod_cast h` instead.

4. For `erdos_bound_false`: choose threshold = max N (⌈exp(exp(C/δ))⌉₊ + 1) to get n with log log n > C/δ. The contradiction is: n^{1+δ} ≤ ν(n) ≤ n^{1+C/log log n} forces δ ≤ C/log log n, but log log n > C/δ means δ·log log n > C.

5. The project uses `noncomputable` throughout (classical decidability for ℝ).  This is fine — `Finset.filter` works with classical `Decidable` instances.

6. Commit often with descriptive messages.  Always end commits with the co-author line.

## Memory

Persistent memory is at `/Users/khanh/.claude/projects/-Volumes-Hippopotamus-vault-code-erd46/memory/`.  Store user preferences, project decisions, and non-obvious context there.
