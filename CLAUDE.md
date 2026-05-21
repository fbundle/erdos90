# CLAUDE.md — Instructions for continuing this Lean 4 formalization

## What this project is

A Lean 4 formalization of Theorem 1.1 from the OpenAI paper *"Planar Point Sets with Many Unit Distances"* (2026).  The theorem disproves the Erdős unit-distance conjecture:

> ∃ δ > 0 such that ν(n) ≥ n^{1+δ} for infinitely many n.

Here ν(n) = maximum number of unit-distance pairs among n points in the plane.

## File structure

| File | Purpose |
|------|---------|
| `Erdos90/Defs.lean` | Geometric primitives (`polydisc`, `shift`, `rho`, `CosetAvgWitness`) + core definitions (`distSq`, `unitDistPairs`, `maxUnitDists`) |
| `Erdos90/Arithmetic.lean` | `AdmissibleFamily` structure (no axioms — `exists_admissible_family` is a theorem in NumberField) |
| `Erdos90/NumberField.lean` | Theorem `exists_admissible_family` proved from 3 sub-axioms + analytic lemmas |
| `Erdos90/Geometric.lean` | `GoodCoset`, `exists_good_coset` (def), lemmas, Theorems 2.3a/b |
| `Erdos90/Main.lean` | Theorem 1.1 (`erdos_unit_distance_false`) + contrapositive |
| `Erdos90/Axioms.lean` | Human-readable documentation of the 3 remaining sub-axioms |
| `Erdos90.lean` | Root import (imports all modules, including NumberField) |
| `lakefile.toml` | Build configuration (mathlib dependency, library target `Erd46`) |

## Rules

**Read `README.md` before doing anything.**  It contains project constraints and conventions set by the human maintainer.  Do not duplicate its content here — read it directly.

In particular: never edit or commit `README.md` itself.

## Build

```bash
lake build
```

Requires `leanprover/lean4:v4.29.1` and mathlib (declared in `lakefile.toml`).  The build succeeds with zero `sorry` gaps.

## The 2 remaining axioms

There are **2 remaining axioms** (down from 5 original, and 7 in the peak decomposition), both in `Erdos90/NumberField.lean`:

1. **`prop_3_2_to_3_6`** — Golod–Shafarevich / Chebotarev tower construction.  Produces `C_rd > 0` and for `ℓ ≥ 2`: `D₀`, `rd_F` with `log rd_F ≤ C_rd·ℓ·log ℓ`, and for every M: degree `f ≥ M` + lattice `Λ ⊂ ℂ^f` with D₀-separation.  (Absent from Mathlib: Golod-Shafarevich [GS64], Chebotarev [Tsc26], class field towers.)

2. **`prop_2_2`** — Class-group pigeonhole + coset averaging (Prop 2.2 + Lemma 2.4).  Produces `U ⊂ ℂ^f` with all-coordinate modulus 1, `D₀·u ∈ Λ`, `|U| ≥ exp((t·log 2 − log_H)·f)`, and `Nonempty` of the coset averaging witness function.  `Classical.choice` recovers the witness in the noncomputable section.

`C_class := 1` (concrete `def`, not axiom).  `C₀`, `prop_3_7`, and `prop_2_2_covg` were removed/absorbed.

All other statements (analytic lemmas, geometric constructions, Theorem 1.1) are fully proven in Lean.

## Current proof state (everything is proven)

### Fully proven
- `projection_injective` — first-coordinate projection injective on a Λ-coset (Lemma 2.5)
- `card_ordered_unit_pairs_eq_two_mul_unitDistPairs` — swap involution + strong induction
- `distSq_symm` — symmetry of Euclidean distance
- `unitDistPairs_le_maxUnitDists` — any finite planar set achieves ≤ maxUnitDists
- `size_bound` — sup-norm packing: |X| ≤ exp(2f·log(4RD+1)), proven via grid discretization
- `first_coordinate_separation` — for nonzero v ∈ Λ, ‖v(fin0 A.hf)‖ ≥ D⁻¹
- `exists_R_log_rho_gt` — ∀ ε>0, D>0, ∃ R>½, log ρ(R) > −ε ∧ 4RD > 1 (from ρ(R) → 1)
- `tendsto_rho_atTop` — ρ(R) → 1 as R → ∞
- `rho_formula` — algebraic simplification of ρ(R)
- **`exists_good_coset`** — now a `def` (not `axiom`): unpacks `A.h_coset_avg` into a `GoodCoset`
- `planar_set_from_datum` (Theorem 2.3 parametric) — fully proven
- `admissible_family_to_planar_set` (Theorem 2.3) — fully proven
- `erdos_unit_distance_false` (Theorem 1.1) — fully proven; B = 2·log(4RD+1), δ = γ/(4B)
- `erdos_bound_false` (contrapositive) — fully proven

### Deep axioms (declared as `axiom` in `NumberField.lean`, awaiting human verification)
- `prop_3_2_to_3_6` — Golod–Shafarevich / Chebotarev tower construction
- `prop_2_2` — Class-group pigeonhole + coset averaging (via Nonempty)

### Theorem (proved from the 2 axioms above)
- `exists_admissible_family` — ∃ γ>0, D>0, ∀ M, ∃ A with A.f ≥ M, A.γ = γ, A.D = D

### Removed/absorbed
- `C_class := 1` (concrete `def`, not axiom)
- `C₀` — redundant (absorbed into prop_3_2_to_3_6)
- `prop_3_7` — Minkowski class-number bound (never called; absorbed into prop_2_2 + C_class)
- `prop_2_2_covg` — combined into prop_2_2 via `Nonempty` (classical equivalence)

There are zero `sorry` gaps and 2 axioms.

## Important types and notations

- `AdmissibleFamily` has fields: `f`, `hf`, `D`, `hD`, `γ`, `hγ`, `Λ` (AddSubgroup), `U` (Finset), `hU_mod`, `hU_in_Λ`, `hU_size`, `hΛ_sep`, `h_coset_avg`
- `h_coset_avg` field: `∀ R, R > 1/2 → log(rho R) > −γ/2 → CosetAvgWitness f Λ U R γ`
- `CosetAvgWitness f Λ U R γ` — structure in `Defs.lean` packaging coset averaging data (fields: `a`, `X`, `hX_sub`, `hX_fin`, `hX_ne`, `h_count`)
- `fin0 hf` is the first element of `Fin f` (guards f ≥ 1)
- `polydisc f R` — sup-norm polydisc in ℂ^f (defined in `Defs.lean`)
- `shift a S` — translation of set S by vector a (defined in `Defs.lean`)
- `rho R` — disc-overlap ratio a(R)/b(R) (defined in `Defs.lean`)
- `distSq` — squared Euclidean distance on ℝ×ℝ
- `unitDistPairs P` — counts *unordered* unit-distance pairs (filtered offDiag / 2)
- `GoodCoset A R` — packages the coset averaging result; constructed by `exists_good_coset` from `A.h_coset_avg`
- `planar_set_from_datum A R hR hρ h_4RD` — parametric Theorem 2.3; outputs |P| ≥ 1, |P| ≥ exp(γ/2·f), |P| ≤ exp(2·log(4RD+1)·f), ν(P) ≥ ½·exp·|P|
- `admissible_family_to_planar_set A` — picks R internally, outputs ν(P) ≥ ½·|P|^{1+2δ}

## Key Mathlib API facts (non-obvious)

- `‖z‖^2 = normSq z` for `z : ℂ`: use `simp [Complex.norm_def, Real.sq_sqrt (normSq_nonneg _)]` — **`Complex.abs`, `Complex.abs_apply`, `Complex.norm_eq_abs` do NOT exist** in this Mathlib version
- `Real.rpow_def_of_pos hx (e) : x^e = exp(log x * e)` — note multiplication order (log x * e, not e * log x)
- `Real.rpow_le_rpow_left_iff (h : 1 < b) : b^x ≤ b^y ↔ x ≤ y`
- `one_lt_exp_iff.mpr hx : exp x > 1` when `x > 0` — **`Real.one_lt_exp` does NOT exist**
- `Nat.le_ceil x : x ≤ ⌈x⌉₊` (for ceiling)
- `Int.card_Ico` — cardinality of `Finset.Ico (a : ℤ) (b : ℤ)` = `(b - a).toNat`
- `abs_le.mp` — splits `|a| ≤ b` into `-b ≤ a ∧ a ≤ b`
- `abs_re_le_norm` / `abs_im_le_norm` — `|z.re| ≤ ‖z‖` and `|z.im| ≤ ‖z‖` for `z : ℂ`
- Local `let` bindings are NOT unfolded by `simp only` or `dsimp only` — use `.mp` / `.mpr` directly
- `positivity` can't prove `R > 0` from `4*R*A.D > 1` and `A.D > 0` — use explicit `by_contra` + `nlinarith`
- `GoodCoset A R` is a `Type` not `Prop` — use `def` not `theorem/lemma` when returning it; can't use `obtain`/tactic `cases` to eliminate into it

## Tips for continuing

1. **Don't touch README.md.**  Ever.

2. The `swap` involution proof for even cardinality used `Finset.strongInductionOn` with a generalized induction hypothesis (`revert` trick).  This pattern works for similar combinatorial arguments.

3. The `Nat.cast_le.mp` typeclass can get stuck — use `have h : (N : ℝ) ≤ (P.card : ℝ) := ?_; exact_mod_cast h` instead.

4. The project uses `noncomputable` throughout (classical decidability for ℝ).  This is fine — `Finset.filter` works with classical `Decidable` instances.

5. Commit often with descriptive messages.  Always end commits with the co-author line.

## Memory

Persistent memory is at `/Users/khanh/.claude/projects/-Volumes-Hippopotamus-vault-code-erd46/memory/`.  Store user preferences, project decisions, and non-obvious context there.
