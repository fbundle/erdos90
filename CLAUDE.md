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
| `Erd46/Geometric.lean` | Axioms 2–5, `GoodCoset`, Theorem 2.3 (planar set from family) |
| `Erd46/Main.lean` | Theorem 1.1 (`erdos_unit_distance_false`) + contrapositive |
| `Erd46/Axioms.lean` | Human-readable index of all 5 axioms with mathematical context |
| `Erd46.lean` | Root import (imports all modules) |
| `lakefile.toml` | Build configuration (mathlib dependency, library target `Erd46`) |

## Rules

**Read `README.md` before doing anything.**  It contains project constraints and conventions set by the human maintainer.  Do not duplicate its content here — read it directly.

In particular: never edit or commit `README.md` itself.

Commit messages must end with `Co-Authored-By: DeepSeek-V4-Pro with Claude Code`.

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

### Deep axioms (`sorry` — awaiting human verification)
- `exists_admissible_family` (Axiom 1)
- `exists_good_coset` (Axiom 3)
- `size_bound` (Axiom 4)

### Arithmetic / combinatorial gaps (`sorry` — routine but tedious)
These are inside `admissible_family_to_planar_set` (`Geometric.lean` ~lines 290–385):

- **`h_card_le`**: the projection φ(x,y) = (re_im(π₁ x), re_im(π₁ y)) injects the set of U-pairs in X into the set of ordered unit-distance pairs in P.  Needs `Finset.card_le_card_of_injOn` or similar.  The map is injective because π₁ is injective on X and re_im is injective on ℂ.  Distance preservation: ‖u(fin0)‖ = 1 for u ∈ U.

- **`h_exp_bound`**: from `|P| ≤ exp(B·f)` and `γ/2 = 2δB`, derive `exp(γf/2) ≥ |P|^{2δ}`.  Uses `Real.log` monotonicity and the identity `exp(a·log x) = x^a`.  Also needs the final `rpow` step: `|P|^{2δ}·|P| = |P|^{1+2δ}`.

### Final theorem gaps (`sorry` in `Main.lean`)

- **`erdos_unit_distance_false`**: needs to extract the lower bound `|P| ≥ exp(γf/2)` from the counting estimate (E ≤ |P|² and E ≥ exp(γf/2)·|P| ⇒ |P| ≥ exp(γf/2)), then pick f large enough that `|P|^δ ≥ 2` so `½·|P|^{1+2δ} ≥ |P|^{1+δ}`.

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

## Tips for continuing

1. **Don't touch README.md.**  Ever.

2. The `swap` involution proof for even cardinality used `Finset.strongInductionOn` with a generalized induction hypothesis (`revert` trick).  This pattern works for similar combinatorial arguments.

3. For the `h_card_le` gap (injection on pairs), define φ(x,y) = (re_im(π₁ x), re_im(π₁ y)), prove it maps E_finset into E_ord, and use `Finset.card_le_card_of_injOn` or `card_image_of_injOn` + `card_le_card_of_subset`.

4. For `h_exp_bound`, the chain is: `log|P| ≤ B·f` (from size_bound), multiply by `2δ` to get `2δ·log|P| ≤ 2δ·B·f = γ/2·f` (using `h_γ_over_2_eq_2δB`), then exponentiate.

5. The project uses `noncomputable` throughout (classical decidability for ℝ).  This is fine — `Finset.filter` works with classical `Decidable` instances.

6. Commit often with descriptive messages.  Always end commits with the co-author line.

## Memory

Persistent memory is at `/Users/khanh/.claude/projects/-Volumes-Hippopotamus-vault-code-erd46/memory/`.  Store user preferences, project decisions, and non-obvious context there.
