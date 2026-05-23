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
| `Erdos90/NumberField.lean` | Theorem `exists_admissible_family` + analytic lemmas (`prop_p6`, `hlog2_event`); calls `prop_3_2_to_3_6_via_deep` from NumberFieldDeep |
| `Erdos90/NumberFieldDeep.lean` | Deep number theory in 7 sections: §1 analytic helpers (proved), §2 GS tower (`GSBaseData` + `GSTowerData`; `gs_base_construction` + `gs_tower_levels`, both sorry'd), §3 pigeonhole (`exists_fiber_ge_div`, proved), §4 CM lemmas (4 fully proved: `norm_div_star_eq_one`, `cm_norm_div_conj_eq_one`, `normAtPlace_mixedEmbedding_cm_div_conj_eq_one`, `mixedEmbedding_cm_div_conj_complex_norm_one`), §5 `CMClassGroupData` + `exists_cm_class_group_data` (sorry'd), §6 `cm_norm_one_elements` (proved modulo §5), §7 `prop_3_2_to_3_6_via_deep` (proved modulo §2+§5) |
| `Erdos90/CosetAveraging.lean` | `lemma_2_4` — coset averaging (fully proved) |
| `Erdos90/Geometric.lean` | `GoodCoset`, `exists_good_coset` (def), lemmas, Theorems 2.3a/b |
| `Erdos90/DiscGeometry.lean` | Discrete geometry lemmas |
| `Erdos90/Main.lean` | Theorem 1.1 (`erdos_unit_distance_false`) + contrapositive |
| `Erdos90.lean` | Root import (imports all modules) |
| `lakefile.toml` | Build configuration (mathlib dependency, library target `Erd46`) |

## Rules

**Read `README.md` before doing anything.**  It contains project constraints and conventions set by the human maintainer.  Do not duplicate its content here — read it directly.

In particular: never edit or commit `README.md` itself.

## Build

```bash
lake build
```

Requires `leanprover/lean4:v4.29.1` and mathlib (declared in `lakefile.toml`).  The build succeeds with 3 `sorry` gaps.

## Proof state — zero axioms, 3 `sorry` gaps

All number-theoretic postulates are `def`s with `sorry` bodies (zero `axiom` keywords). The build succeeds; `erdos_unit_distance_false` depends only on `sorryAx` + foundational Lean axioms (no custom axioms).

All three sorries are in **`Erdos90/NumberFieldDeep.lean`**:

### `def` with `sorry` (deep number theory, requires new Mathlib development)

**`gs_base_construction`** (line ~101) — Golod–Shafarevich base data, Props 3.2–3.5

Lean gaps:
- Cyclic cubic field F from ℓ primes r_i ≡ 1 (mod 3)
- Golod–Shafarevich: pro-3 group theory, relation-rank estimate r ≤ d²/4 (not in Mathlib)
- Shafarevich bound r(G) ≤ d(G) + C₀ (not in Mathlib)
- D₀ = Q² (product of split Chebotarev primes squared)

**`gs_tower_levels`** (line ~117) — Chebotarev tower levels + Minkowski lattice, Prop 3.6

Lean gaps:
- Quantitative Chebotarev: build infinite tower from G̅ (not in Mathlib)
- Type bridge: `mixedSpace K ≃ Fin f → ℂ` for totally complex CM field K
- Transport of `integerLattice` + `IsAddFundamentalDomain` + separation across the isomorphism

**`exists_cm_class_group_data`** (line ~411) — CM field / class-group data for Prop 2.2

Lean gaps:
- CM field K of degree 2f with split-prime ideal pairs (𝔓_j, c𝔓_j) (no CM split-prime API in Mathlib)
- Class-number bound |G| ≤ exp(log_H·f) from Minkowski / tower root-discriminant
- Norm-1 element constructor: α/c(α) using `IsCMField.complexConj` (core CM lemmas proved in §4)
- Injectivity: α/c(α) = β/c(β) ⇒ α/β ∈ K⁺ ⇒ ε₂ = ε₃

**Assembly functions** (no additional sorries):
- `golod_shafarevich_tower_with_lattice ℓ hℓ : GSTowerData ℓ` — clean `let`-based assembly of `gs_base_construction` + `gs_tower_levels`
- `prop_3_2_to_3_6_via_deep` — chains the tower data with `cm_norm_one_elements` (§7)

Relevant Mathlib (available but incomplete): `IsCyclotomicExtension.Rat.isCMField`, `NumberField.classNumber`, `NumberField.exists_ideal_in_class_of_norm_le`, `IsCMField.complexConj`, `IsCMField.complexEmbedding_complexConj`, `fundamentalDomain_integerLattice`, `volume_fundamentalDomain_latticeBasis`, `ZSpan.isAddFundamentalDomain`

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
- `prop_p6` — analytic lemma: (ℓ-1)²·log 2 > C·ℓ·log ℓ for large ℓ (in NumberField.lean)
- `hlog2_event` — log 2 ≤ C_rd·k·log k for large k (in NumberField.lean)
- `exists_good_coset` — unpacks `A.h_coset_avg` into `GoodCoset`
- `planar_set_from_datum` (Theorem 2.3 parametric) — fully proven
- `admissible_family_to_planar_set` (Theorem 2.3) — fully proven
- `erdos_unit_distance_false` (Theorem 1.1) — fully proven
- `erdos_bound_false` (contrapositive) — fully proven
- `lemma_2_4` — coset averaging (CosetAveraging.lean, fully proved)
- `h_ineq` / `h_unfold_vol` / `h_unfold` / `h_int_N` / `h_int_Eu` / `h_int_ineq` within `lemma_2_4` — all sub-steps fully proved
- `disc_overlap_ratio_real` — area of intersection of two ℂ-discs = πR²·ρ(R)
- `polydisc_overlap_ratio_real` — Fubini product extension
- `hrho_pos` — positivity of ρ(R) for R > 1/2
- `exists_fiber_ge_div` — pigeonhole lemma (NumberFieldDeep.lean §3, fully proved)
- `norm_div_star_eq_one` — pure complex analysis: ‖z / star z‖ = 1 (NumberFieldDeep.lean §4, fully proved)
- `cm_norm_div_conj_eq_one` — ‖φ(α / c(α))‖ = 1 at each complex embedding (NumberFieldDeep.lean §4, fully proved)
- `normAtPlace_mixedEmbedding_cm_div_conj_eq_one` — normAtPlace = 1 under mixedEmbedding (NumberFieldDeep.lean §4, fully proved)
- `mixedEmbedding_cm_div_conj_complex_norm_one` — concrete ‖.2 w‖ = 1 per complex place (NumberFieldDeep.lean §4, fully proved)
- `cm_norm_one_elements` — class-group pigeonhole → norm-one set U (NumberFieldDeep.lean §6, proved modulo `exists_cm_class_group_data`)
- `prop_3_2_to_3_6_via_deep` — assembly theorem (NumberFieldDeep.lean §7, proved modulo three sorries)
- `log_two_mul_le` — analytic helper (NumberFieldDeep.lean §1)

### Auxiliary defs
- `C_class := 1` (concrete `def`)
- `polydisc_measurable` — lemma (fully proved)
- `GSTowerData ℓ` — structure abstracting the Golod–Shafarevich tower output (fields: `D₀`, `hD₀_pos`, `rd_F`, `hrd_F_ge1`, `hlog_rd`, `getTowerLevel`)
- `GSBaseData ℓ` — structure for Props 3.2–3.5 base field data (fields: `D₀`, `hD₀_pos`, `rd_F`, `hrd_F_ge1`, `hlog_rd`)
- `CMClassGroupData f t log_H Λ` — structure abstracting the CM field / class-group input for Prop 2.2 (fields: `E`, `G`, `φ`, `cardE`, `cardG`, `hcardE`, `hcardG`, `h_card_ratio`, `mk_unit`, `mk_unit_mem_Λ`, `mk_unit_norm`, `mk_unit_inj`)

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

### Typeclass instance identity: use `letI` not `haveI`

When a structure carries typeclass fields (e.g., `CMClassGroupData` has `[fintypeE : Fintype E]`), surface them with **`letI`** (not `haveI`):

```lean
-- CORRECT: letI — transparent binder, kernel can unfold to data.fintypeE
letI : Fintype data.E := data.fintypeE

-- WRONG: haveI — opaque binder, NOT def-eq to data.fintypeE, breaks simpa/rw
haveI : Fintype data.E := data.fintypeE
```

`letI` creates a `let` binder that is definitionally equal to the structure projection. The kernel can unfold it, so `Fintype.card data.E` (via `letI`) is def-eq to `Fintype.card data.E` (via `data.fintypeE`). With `haveI`, the binder is opaque and `simpa [data.hcardE]` fails with instance mismatch.

### Number field API (relevant to remaining sorries)

All in `vendor/mathlib4/Mathlib/NumberTheory/NumberField/`:
- `mixedSpace K = ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)` — NOT the same as `Fin f → ℂ`; for totally complex K need `Fintype.equivFin` + `LinearEquiv.piCongrLeft` to bridge
- `fundamentalDomain_integerLattice` in `CanonicalEmbedding/Basic.lean` — `IsAddFundamentalDomain (integerLattice K) (ZSpan.fundamentalDomain (latticeBasis K))`
- `volume_fundamentalDomain_latticeBasis` in same file — `volume (fundamentalDomain (latticeBasis K)) = (2)⁻¹^nrComplexPlaces K * sqrt ‖discr K‖₊`
- `discr_prime_pow` in `Cyclotomic/Discriminant.lean` — explicit discriminant formula for ℚ(ζ_{p^k})
- `IsCyclotomicExtension.isCMField` in `NumberField/Cyclotomic/Basic.lean` — cyclotomic extensions ℚ(ζ_n) with n > 2 are CM
- `exists_ideal_in_class_of_norm_le` in `ClassNumber.lean` — every ideal class has a rep with norm ≤ Minkowski bound
- `integerLattice K : Submodule ℤ (mixedSpace K)` (not `AddSubgroup`); convert via `Submodule.toAddSubgroup`

## Tips for continuing

1. **Don't touch README.md.**  Ever.

2. The `swap` involution proof for even cardinality used `Finset.strongInductionOn` with a generalized induction hypothesis (`revert` trick).  This pattern works for similar combinatorial arguments.

3. The `Nat.cast_le.mp` typeclass can get stuck — use `have h : (N : ℝ) ≤ (P.card : ℝ) := ?_; exact_mod_cast h` instead.

4. The project uses `noncomputable` throughout (classical decidability for ℝ).  This is fine — `Finset.filter` works with classical `Decidable` instances.

5. The three sorries are genuinely deep: Golod–Shafarevich pro-p group theory, quantitative Chebotarev, and CM field split-prime API. None exist in Mathlib v4.29.1.  The rest of the formalization is ready — only the algebraic number theory input is missing.

6. **∃ elimination into Type:** `Exists.casesOn` only eliminates into `Prop` in Lean 4.  When constructing a structure with `ℝ` or other non-`Prop` fields, use helper structures (like `GSBaseData`) instead of `∃` existential hypotheses — otherwise `obtain`/`cases` fails with "recursor can only eliminate into Prop".

7. Commit often with descriptive messages.  Always end commits with the co-author line.

## Memory

Persistent memory is at `/Users/khanh/.claude/projects/-Volumes-Hippopotamus-vault-code-erd46/memory/`.  Store user preferences, project decisions, and non-obvious context there.
