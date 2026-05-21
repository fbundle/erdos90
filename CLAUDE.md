# CLAUDE.md — Instructions for continuing this Lean 4 formalization

## What this project is

A Lean 4 formalization of Theorem 1.1 from the OpenAI paper *"Planar Point Sets with Many Unit Distances"* (2026).  The theorem disproves the Erdős unit-distance conjecture:

> ∃ δ > 0 such that ν(n) ≥ n^{1+δ} for infinitely many n.

Here ν(n) = maximum number of unit-distance pairs among n points in the plane.

## File structure

| File | Purpose |
|------|---------|
| `Erd46/Defs.lean` | Core definitions: `distSq`, `unitDistPairs`, `maxUnitDists` |
| `Erd46/Arithmetic.lean` | `AdmissibleFamily` structure + Axiom 1 (tower existence) |
| `Erd46/Geometric.lean` | Axioms 2–5, `GoodCoset`, Theorems 2.3a/b (planar set from family) |
| `Erd46/Main.lean` | Theorem 1.1 (`erdos_unit_distance_false`) + contrapositive |
| `Erd46/Axioms.lean` | Human-readable index of all 5 axioms with mathematical context |
| `Erd46.lean` | Root import (imports all modules) |
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
- **`h_P_lower`** (inside `planar_set_from_datum`) — |P| ≥ exp(γ/2·f), proved from E ≤ N² and E ≥ exp·N
- **rpow identity** (inside `admissible_family_to_planar_set`) — (P.card)^(2δ)·P.card = (P.card)^(1+2δ), proved via `Real.rpow_add` + `Real.rpow_one`

### Deep axioms (`sorry` — awaiting human verification)
- `exists_admissible_family` (Axiom 1)
- `exists_good_coset` (Axiom 3)
- `size_bound` (Axiom 4)

### Combinatorial gap (`sorry` — routine but tedious)

- **`h_card_le`** (inside both `planar_set_from_datum` and `admissible_family_to_planar_set`): the map φ(x,y) = (re_im(π₁ x), re_im(π₁ y)) injects U-pairs in X into ordered unit-distance pairs in P.
  - Distance: y - x ∈ U ⇒ ‖u(fin0)‖ = 1 ⇒ distSq(re_im(π₁ x), re_im(π₁ y)) = 1
  - Injectivity: π₁ injective on X (proven), re_im injective on ℂ (proven); product is injective
  - Use `Finset.card_le_card_of_injOn` or `card_image_of_injOn` + `card_le_card_of_subset`

- **`h_exp_bound`** (inside `admissible_family_to_planar_set`): from `|P| ≤ exp(B·f)` and `γ/2 = 2δB`, derive `exp(γf/2) ≥ |P|^{2δ}`.
  - Chain: `log|P| ≤ B·f` → multiply by `2δ` → `2δ·log|P| ≤ γ/2·f` → exponentiate → `|P|^{2δ} ≤ exp(γf/2)`
  - Key: `Real.rpow_def_of_pos`, `Real.log_le_log`, `Real.exp_le_exp`, `Real.exp_log`

### Final theorem gaps (`sorry` in `Main.lean`)

- **`erdos_unit_distance_false`**: structure is in place (fixed global R, defined δ = γ/(4B)).  Missing: pick f large enough that exp(γ/2·f) ≥ N and |P|^δ ≥ 2; use `planar_set_from_datum` with rewritten hypotheses (A.γ = γ, A.D = D); combine bounds to get ν(P) ≥ |P|^{1+δ} and |P| ≥ N.

- **`erdos_bound_false`**: asymptotics — pick n large enough that `log log n > C/δ`, then `n^{1+δ} ≤ ν(n) ≤ n^{1 + C/log log n}` gives contradiction.

## Important types and notations

- `AdmissibleFamily` has fields: `f`, `hf`, `D`, `hD`, `γ`, `hγ`, `Λ` (AddSubgroup), `U` (Finset), `hU_mod`, `hU_in_Λ`, `hU_size`, `hΛ_sep`
- `fin0 hf` is the first element of `Fin f` (guards f ≥ 1)
- `polydisc f R` is the sup-norm polydisc in ℂ^f
- `shift a S` is translation of set S by vector a
- `distSq` is squared Euclidean distance on ℝ×ℝ
- `unitDistPairs P` counts *unordered* unit-distance pairs (filtered offDiag / 2)
- `GoodCoset A R` packages the coset averaging result
- `rho R` is the disc-overlap ratio a(R)/b(R)
- `planar_set_from_datum A R hR hρ h_4RD` — parametric form of Theorem 2.3 (R explicit, outputs |P| ≥ exp(γ/2·f) and ν(P) ≥ ½·exp·|P|)
- `admissible_family_to_planar_set A` — corollary that picks R internally and outputs ν(P) ≥ ½·|P|^{1+2δ}

## Tips for continuing

1. **Don't touch README.md.**  Ever.

2. The `swap` involution proof for even cardinality used `Finset.strongInductionOn` with a generalized induction hypothesis (`revert` trick).  This pattern works for similar combinatorial arguments.

3. For `h_card_le`: define φ as a function `(Fin A.f → ℂ) × (Fin A.f → ℂ) → (ℝ × ℝ) × (ℝ × ℝ)` by φ(x,y) = (re_im(π₁ x), re_im(π₁ y)).  Prove `φ '' E_finset.toSet ⊆ E_ord.toSet` (membership check: offDiag + distSq = 1), then `InjOn φ E_finset.toSet` (product of injections), then use `Finset.card_le_card_of_injOn` or image cardinality.

4. For `h_exp_bound`: the chain is `log(P.card) ≤ B·f` (from `h_size` via `Real.log_le_log`), then `2δ · log(P.card) ≤ γ/2 · f` (using `h_γ_over_2_eq_2δB`), then `Real.rpow_def_of_pos` rewrites `|P|^{2δ} = exp(2δ · log|P|)`, and `Real.exp_le_exp` closes the goal.

5. For `erdos_unit_distance_false`: after obtaining A with A.γ = γ and A.D = D, rewrite `hρ_global` and `h_4RD_gt_one` using these equalities before calling `planar_set_from_datum`.  For the choice of M: use `Nat.ceil` or `⌈(2/γ) * Real.log (max N 1)⌉ + 1` and prove `exp(γ/2 · M) ≥ N` using `Real.add_one_le_exp` or monotonicity.

6. The project uses `noncomputable` throughout (classical decidability for ℝ).  This is fine — `Finset.filter` works with classical `Decidable` instances.

7. Commit often with descriptive messages.  Always end commits with the co-author line.

## Memory

Persistent memory is at `/Users/khanh/.claude/projects/-Volumes-Hippopotamus-vault-code-erd46/memory/`.  Store user preferences, project decisions, and non-obvious context there.
