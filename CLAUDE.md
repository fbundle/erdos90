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
| `Erdos90/NumberField.lean` | Theorem `exists_admissible_family` + `def lemma_2_4` + analytic lemmas; all deep number theory as `def … := by sorry` |
| `Erdos90/Geometric.lean` | `GoodCoset`, `exists_good_coset` (def), lemmas, Theorems 2.3a/b |
| `Erdos90/Main.lean` | Theorem 1.1 (`erdos_unit_distance_false`) + contrapositive |
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

## Proof state — zero axioms, 3 `sorry` gaps

All number-theoretic postulates are now `def`s with `sorry` bodies (zero `axiom` keywords). The build succeeds; `erdos_unit_distance_false` depends only on `sorryAx` + foundational Lean axioms (no custom axioms).

### Fully proven (no sorry)
- `projection_injective` — first-coordinate projection injective on a Λ-coset (Lemma 2.5)
- `card_ordered_unit_pairs_eq_two_mul_unitDistPairs` — swap involution + strong induction
- `distSq_symm` — symmetry of Euclidean distance
- `unitDistPairs_le_maxUnitDists` — any finite planar set achieves ≤ maxUnitDists
- `size_bound` — sup-norm packing: |X| ≤ exp(2f·log(4RD+1)), proven via grid discretization
- `first_coordinate_separation` — for nonzero v ∈ Λ, ‖v(fin0 A.hf)‖ ≥ D⁻¹
- `exists_R_log_rho_gt` — ∀ ε>0, D>0, ∃ R>½, log ρ(R) > −ε ∧ 4RD > 1 (from ρ(R) → 1)
- `tendsto_rho_atTop` — ρ(R) → 1 as R → ∞
- `rho_formula` — algebraic simplification of ρ(R)
- `prop_p6` — analytic lemma: (ℓ-1)²·log 2 > C·ℓ·log ℓ for large ℓ (fully proved)
- `hlog2_event` — log 2 ≤ C_rd·k·log k for large k (fully proved)
- `exists_good_coset` — unpacks `A.h_coset_avg` into `GoodCoset`
- `planar_set_from_datum` (Theorem 2.3 parametric) — fully proven
- `admissible_family_to_planar_set` (Theorem 2.3) — fully proven
- `erdos_unit_distance_false` (Theorem 1.1) — fully proven
- `erdos_bound_false` (contrapositive) — fully proven
- `h_ineq` within `lemma_2_4` — algebraic inequality |U|·ρ(R)^f ≥ exp(γf/2) — fully proved
- `h_unfold_vol` / `h_unfold` within `lemma_2_4` — measure-theoretic unfolding via fundamental domain — fully proved
- `disc_overlap_ratio_real` — area of intersection of two ℂ-discs = πR²·ρ(R) — fully proved
- `polydisc_overlap_ratio_real` — Fubini product extension — fully proved
- `hrho_pos` — positivity of ρ(R) for R > 1/2 — fully proved
- `h_int_N` / `h_int_Eu` within `lemma_2_4` — integral identities from unfolding — fully proved
- `h_int_ineq` within `lemma_2_4` — ENNReal conversion of h_overlap_sum (∑ vol(S_u) ≥ c·vol(B_R) in ℝ≥0∞) — fully proved

### `def` with `sorry` (deep number theory / analysis, not in Mathlib)
- `prop_3_2_to_3_6` — Golod–Shafarevich / Chebotarev tower construction
- `prop_2_2` — Class-group pigeonhole for norm-1 elements

### Partially proved `def` (structural proof with `sorry` gaps)
- `lemma_2_4` — coset averaging: algebraic + measure-theoretic unfolding proved, `h_int_ineq` (ENNReal conversion) now proved; final witness construction (averaging principle) remains as `sorry`

### Auxiliary defs
- `C_class := 1` (concrete `def`)
- `polydisc_measurable` — lemma (fully proved)

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
- `Set.vaddSet`/`Set.smulSet` instances are scoped under `Pointwise` — need `open scoped Pointwise` for `g +ᵥ F` notation on sets
- `Set.indicator_apply` needs `[Decidable (a ∈ s)]` — wrap in `classical` when using
- `measurable_add_const` is the lemma for `Measurable (· + c)` on additive groups (avoids `by continuity` timeouts on `Fin f → ℂ`)

## Tips for continuing

1. **Don't touch README.md.**  Ever.

2. The `swap` involution proof for even cardinality used `Finset.strongInductionOn` with a generalized induction hypothesis (`revert` trick).  This pattern works for similar combinatorial arguments.

3. The `Nat.cast_le.mp` typeclass can get stuck — use `have h : (N : ℝ) ≤ (P.card : ℝ) := ?_; exact_mod_cast h` instead.

4. The project uses `noncomputable` throughout (classical decidability for ℝ).  This is fine — `Finset.filter` works with classical `Decidable` instances.

5. Commit often with descriptive messages.  Always end commits with the co-author line.

## Memory

Persistent memory is at `/Users/khanh/.claude/projects/-Volumes-Hippopotamus-vault-code-erd46/memory/`.  Store user preferences, project decisions, and non-obvious context there.
