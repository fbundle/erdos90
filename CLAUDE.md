# CLAUDE.md — Instructions for continuing this Lean 4 formalization

## What this project is

A Lean 4 formalization of Theorem 1.1 from the OpenAI paper *"Planar Point Sets with Many Unit Distances"* (2026), which disproves the Erdős unit-distance conjecture:

> ∃ δ > 0 such that ν(n) ≥ n^{1+δ} for infinitely many n.

`ν(n)` = max unit-distance pairs among `n` planar points.  Main theorem: `Erdos90.Main.erdos_unit_distance_false`.

## Rules

**Read `README.md` first.** Never edit or commit `README.md` — it is the human maintainer's file.

## File structure

| File | Purpose |
|------|---------|
| `Erdos90/Defs.lean` | Geometric primitives (`polydisc`, `shift`, `rho`, `CosetAvgWitness`) + core definitions (`distSq`, `unitDistPairs`, `maxUnitDists`) |
| `Erdos90/Arithmetic.lean` | `AdmissibleFamily` structure (`exists_admissible_family` is a theorem) |
| `Erdos90/NumberField.lean` | `exists_admissible_family` + analytic lemmas; calls `prop_3_2_to_3_6_via_deep` |
| `Erdos90/NumberFieldDeep.lean` | Import hub re-exporting the split files below |
| `Erdos90/NumberFieldDeep_Analytic.lean` | Analytic helpers (all proved) |
| `Erdos90/NumberFieldDeep_GSTower.lean` | `BRDTowerData` + `brd_tower_data` postulate (decomposed into `gs_cm_tower` + `chebotarev_fixed_Q`); `brd_cm_tower_postulate` body PROVED |
| `Erdos90/NumberFieldDeep_ANT.lean` | ANT infrastructure: `sawin_tower_exists`, `gs_tower_levels_v2`, etc. |
| `Erdos90/NumberFieldDeep_CM.lean` | Pigeonhole + 4 CM lemmas + `CMTowerData`/`CMClassGroupData` + `exists_cm_class_group_data` (fully proved) |
| `Erdos90/NumberFieldDeep_Assembly.lean` | `cm_norm_one_elements` + `prop_3_2_to_3_6_via_deep` + `ant_postulates` |
| `Erdos90/CosetAveraging.lean` | `lemma_2_4` — coset averaging (proved) |
| `Erdos90/Geometric.lean` | `GoodCoset`, Theorems 2.3a/b |
| `Erdos90/DiscGeometry.lean` | Discrete geometry lemmas |
| `Erdos90/Main.lean` | Theorem 1.1 (`erdos_unit_distance_false`) + contrapositive |
| `Erdos90.lean` | Root import |
| `Erdos90/CMField/Basic.lean` | `conjIdeal`, `SplitPrimeData` (with `h_Q_count_*` fields), `count_J_eq` family (all proved) |
| `Erdos90/CMField/CyclotomicSplitPrimes.lean` | Split primes in ℚ(ζ_p); `splitPrimeData_from_prime_list` proved |
| `Erdos90/CMField/QScaling.lean` | Q²-scaling integrality lemma (proved) |
| `Erdos90/CMField/MinkowskiLattice.lean` | Unscaled CM Minkowski lattice (all proved) |
| `Erdos90/CMField/QScalingLattice.lean` | Q²-scaled CM Minkowski lattice on top of MinkowskiLattice (all proved) |
| `Erdos90/Mathlib4_Extra/*.lean` | Mathlib-candidate lemmas + decomposed postulates (see "Postulate layout" below) |
| `lakefile.toml` | Build configuration |

## Build

```bash
lake build
```

Requires `leanprover/lean4:v4.30.0-rc2` and mathlib `master-2026-05-24`.  Build succeeds; `erdos_unit_distance_false` depends only on `[propext, sorryAx, Classical.choice, Quot.sound]` (zero `axiom` keywords).

## Proof state

The main theorem is proved modulo labelled `sorry` postulates that decompose into ever-smaller named sub-postulates.  See `grep -rn ":= sorry" Erdos90/` for the live list.

### Proof path (load-bearing)

- **`gs_cm_tower_infinite_postulate`** in `Mathlib4_Extra/GolodShafarevich.lean` — itself a proved assembly of `gs_base_field_postulate` (proved assembly of `gs_imagquad_with_p_rank_postulate` + `gs_cm_lift_postulate`) and `gs_iterate_postulate` (proved by induction modulo `gs_criterion_inherited_postulate` → `pHCF_p_dvd_classNumber_postulate`, etc.).
- **`chebotarev_fixed_Q`** in `NumberFieldDeep_GSTower.lean` — Chebotarev/Ihara fixed split primes.  Tracked in `Mathlib4_Extra/Chebotarev.lean`.

### Off-path (Mathlib-PR-shaped, future work)

- `regulator_lower_bound_cm` (Friedman 1989) — proved modulo `friedman_regulator_lower_bound_postulate`; `zimmert_regulator_lower_bound_postulate` is the alternate weaker route.
- `dedekind_residue_upper_bound_cm` (Louboutin 2000) — decomposed into `dedekindZeta_functional_equation_postulate` + `phragmen_lindelof_zeta_postulate`.
- `hilbertClassField_exists` / `hilbertPClassField_exists` postulates in `Mathlib4_Extra/ClassFieldTheory.lean`.
- `nat_le_four_mul_totient_sq` (n ≥ 17 case) — pure-Nat Mathlib PR target.

`brd_tower_data` is **proved Lean code** assembling these.  Phase D4 closed the `log_H ≥ 2 · log(2 · rd_F)` threshold by threading the hypothesis from `BRDTowerData.getTowerLevel` up to `exists_admissible_family` (which proves it via `C_class = 1`).

### Proof flow

`brd_tower_data` → `brd_cm_tower_postulate` (PROVED body) → `gs_tower_levels` → `GSTowerData.getTowerLevel` → `prop_3_2_to_3_6_via_deep` → `exists_admissible_family` → `erdos_unit_distance_false`

### Postulate layout in `Mathlib4_Extra/`

- `GolodShafarevich.lean` — GS criterion + decomposed sub-postulates (genus theory, Scholz-Reichardt, CM-lift, p-HCF degree/CM/iso/descent, GS inequality, iteration, base-field).
- `ClassFieldTheory.lean` — HCF + p-HCF structures with Artin reciprocity + `hilbertClassField_exists`/`hilbertPClassField_exists` postulates + proved corollaries (`rootDiscr_hcf_eq`, `card_gal_hcf_eq_classNumber`, `isTotallyComplex`).
- `RayClassField.lean` — `MaxProPExt`, `RayClassField` structures (HMR's S-restricted setting).
- `Chebotarev.lean` — Chebotarev density + Ihara split-primes postulates.
- `UnramifiedDiscriminant.lean` — `rootDiscr_eq_of_unramifiedTower` (PROVED), tower discriminant formula (PROVED).
- `ClassNumberBound.lean` — Brauer–Siegel chain (E1–E12): `classNumber_le_card_ideals_of_norm_le_minkowski` (proved), `minkBound_le_pow_rootDiscr` (proved), `classNumber_eq_residue_formula` (proved), `regulator_lower_bound_cm` (proved modulo Friedman), `dedekind_residue_upper_bound_cm` (sorry, decomposed into FE + Phragmén-Lindelöf), `torsionOrder_bound` (proved), `nat_le_four_mul_totient_sq` (partially proved).
- `DedekindZetaFE.lean` — Dedekind ζ functional equation infrastructure (in progress).
- `NumberFieldTheta.lean`, `HeckeCharacters.lean`, `LocalCFT.lean`, `GlobalCFT.lean`, `Conductor.lean`, `NormGroup.lean`, `Iwasawa.lean`, `LubinTate.lean`, `ProPGalois.lean`, `BrauerGroup.lean`, `HilbertSymbol.lean`, `StarkConjectures.lean`, `Stickelberger.lean`, `ReciprocityLaws.lean`, `TameRamification.lean`, `SelmerGroup.lean` — assorted CFT/L-function stubs for the dependency tree.
- `Analytic.lean`, `FractionalIdealCount.lean`, `FractionalIdealRingEquiv.lean`, `SeparablePoisson2D.lean`, `PoissonProd.lean` — Mathlib-candidate lemmas, all proved (modulo specific PoissonProd sorries).

## Important types and notations

- `AdmissibleFamily`: `f`, `hf`, `D`, `hD`, `γ`, `hγ`, `Λ` (`AddSubgroup`), `U` (`Finset`), `hU_mod`, `hU_in_Λ`, `hU_size`, `hΛ_sep`, `h_coset_avg`.
- `h_coset_avg`: `∀ R, R > 1/2 → log(rho R) > −γ/2 → CosetAvgWitness f Λ U R γ`.
- `CosetAvgWitness f Λ U R γ` (in `Defs.lean`): `a`, `X`, `hX_sub`, `hX_fin`, `hX_ne`, `h_count`.
- `BRDTowerData ℓ`: `Q : ℕ` (fixed across tower), `D₀ = Q²`, `rd_F ≥ 1` with `log rd_F ≤ ℓ · log ℓ`, `getTowerLevel (M, t, log_H, ht, hlog_H_pos, hlog_H_ge_rd)`.
- `CMTowerData f hf1 Λ K`: `φ`, `h_nrComplexPlaces`, `h_nrRealPlaces`, `h_φ1_norm`, `h_φ_norm_div_conj`, `t'_param`, `spData : SplitPrimeData K (t'_param * f)`, `h_div_conj_mem_Λ`, `classNumBound`, `hClassNum`.
- `CMClassGroupData f t log_H Λ`: `E`, `G`, `φ`, `cardE`, `cardG`, `hcardE`, `hcardG`, `h_card_ratio`, `mk_unit`, `mk_unit_mem_Λ`, `mk_unit_norm`, `mk_unit_inj`.
- `fin0 hf` — first element of `Fin f` (guards `f ≥ 1`).
- `polydisc f R`, `shift a S`, `rho R` — defined in `Defs.lean`.
- `unitDistPairs P` — *unordered* unit-distance pairs.
- `GoodCoset A R` — Type (not Prop); use `def` not `theorem`.
- `C_class := 1` (concrete `def`).

## Key Mathlib API gotchas

- `‖z‖^2 = normSq z` for `z : ℂ`: use `simp [Complex.norm_def, Real.sq_sqrt (normSq_nonneg _)]` — **`Complex.abs`, `Complex.abs_apply`, `Complex.norm_eq_abs` do NOT exist**.
- `Real.rpow_def_of_pos hx (e) : x^e = exp(log x * e)` — note multiplication order.
- `one_lt_exp_iff.mpr hx : exp x > 1` when `x > 0` — **`Real.one_lt_exp` does NOT exist**.
- `Int.card_Ico`, `Nat.le_ceil`, `abs_re_le_norm`/`abs_im_le_norm`, `measurable_add_const` — useful idioms.
- Local `let` bindings: NOT unfolded by `simp only`/`dsimp only`; use `.mp`/`.mpr` directly.
- `Set.vaddSet`/`Set.smulSet`: scoped under `Pointwise` — need `open scoped Pointwise`.
- `Set.indicator_apply` needs `[Decidable (a ∈ s)]` — wrap in `classical`.

### `letI` vs `haveI` for structure typeclass fields

```lean
letI : Fintype data.E := data.fintypeE   -- CORRECT: transparent, def-eq to projection
haveI : Fintype data.E := data.fintypeE   -- WRONG: opaque, breaks simpa/rw
```

`letI` is def-eq to the structure projection; `haveI` is opaque and breaks `simpa [data.hcardE]` with an instance mismatch.

### ∃ elimination into `Type`

`Exists.casesOn` only eliminates into `Prop`.  When constructing a structure with `ℝ` or other non-`Prop` fields from an existential, use helper structures or `Classical.choose` — `obtain`/`rcases` will fail with "recursor can only eliminate into Prop".

### Number field API (relevant)

In `vendor/mathlib4/Mathlib/NumberTheory/NumberField/`:
- `mixedSpace K = ({IsReal} → ℝ) × ({IsComplex} → ℂ)` — NOT `Fin f → ℂ`; bridge with `Fintype.equivFin` + `LinearEquiv.piCongrLeft`.
- `fundamentalDomain_integerLattice`, `volume_fundamentalDomain_latticeBasis` (`CanonicalEmbedding/Basic.lean`).
- `discr_prime_pow` (`Cyclotomic/Discriminant.lean`).
- `IsCyclotomicExtension.isCMField` (`NumberField/Cyclotomic/Basic.lean`).
- `exists_ideal_in_class_of_norm_le` (`ClassNumber.lean`).
- `integerLattice K : Submodule ℤ (mixedSpace K)` — convert via `Submodule.toAddSubgroup`.

## Working principles

- **Decompose deeper, not wider**: when a sorry is multi-month/year work, the highest-leverage move is *naming* its sub-postulates with literature citations, not trying to close it.  Same math content, vastly improved legibility and PR-shape.
- **Never pack false statements as structure fields**: a sorried `False` is worse than a sorried `True`.  If a numeric inequality depends on external parameters, lift it to an explicit hypothesis at the boundary.
- **Architectural sorries can be threaded**: if a statement is true-in-practice but not from local hypotheses, push the needed hypothesis through the signature chain to the point where it's provable.
- **`Classical.choose` for Type-valued existentials**: when destructuring `∃ x : Type, ...` to build a structure, use `Classical.choose`/`Classical.choose_spec`, not `obtain`.
- **Commit often** with descriptive messages.  End commit messages with the co-author line.

## External CFT formalization (vendor/)

`vendor/ClassFieldTheory/` is Kevin Buzzard's [ClassFieldTheory project](https://github.com/kbuzzard/ClassFieldTheory), the main repo for the 2025 Clay Maths summer school on formalizing CFT.  It has ~105 Lean files with only ~27 sorries, covering:
- Tate cohomology + finite cyclic + augmentation modules + splitting modules
- Local invariant `H²(ℤ/nℤ, ℤ) ≅ ℤ/nℤ`
- Non-archimedean local fields: valuation, ramification, tower, unramified extensions, Herbrand quotient
- Local CFT building blocks (Continuity, Teichmuller)

**Version mismatch**: Buzzard's repo uses Lean v4.29.0 + Mathlib at commit `3bd2603b81` (≈ v4.29).  Our repo uses Lean v4.30.0 + Mathlib v4.30.0.  Direct import is not possible without aligning toolchain versions.  Useful as reference for: which API names already exist in their formalization, which decompositions they use, which Mathlib lemmas they leverage.

## Memory

Persistent memory is at `/Users/khanh/.claude/projects/-Volumes-Hippopotamus-vault-code-erd46/memory/`.  Store user preferences and non-obvious context there; the README of that directory (`MEMORY.md`) is auto-loaded.
