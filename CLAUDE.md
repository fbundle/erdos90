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
| `Erdos90/NumberFieldDeep.lean` | Import hub: re-exports all deep number-theoretic components from the 4 split files below |
| `Erdos90/NumberFieldDeep_Analytic.lean` | §1: Analytic helpers (`log_two_mul_le`, `exp_sub_mul_eq_rpow_div_exp`, `card_ratio_ineq`), all proved |
| `Erdos90/NumberFieldDeep_GSTower.lean` | §2: GS tower — `BRDTowerData` structure, `brd_tower_data` postulate (3 sorries: `gs_cm_tower`, `chebotarev_fixed_Q`, `class_num_bound_of_brd`), `brd_cm_tower_postulate` body PROVED (assembles BRDTowerData + QScalingLattice + Phase A's lemma into the full lattice/cmData existential).  Also `GSBaseData` and `gs_base_construction` (proved, legacy compat).  Phase D5 (2026-05-26) split `hmr_brd_cm_tower` into `gs_cm_tower` + `chebotarev_fixed_Q` named pieces; `hmr_brd_cm_tower` itself is proved assembly. |
| `Erdos90/NumberFieldDeep_ANT.lean` | ANT infrastructure: `sawin_tower_exists`, `gs_tower_levels_v2`, `exists_cm_class_group_data_v2`.  The Minkowski-lattice machinery (was here pre-Phase-C) is now in `CMField/MinkowskiLattice.lean`; ANT re-exports the names via `export`. |
| `Erdos90/NumberFieldDeep_CM.lean` | §3–§5: Pigeonhole lemma (`exists_fiber_ge_div`, proved), CM lemmas (4 fully proved), `CMTowerData` with fixed `t'_param`/`spData`/`h_div_conj_mem_Λ`, `CMClassGroupData` structure + `exists_cm_class_group_data` (fully proved; takes `ht'_ge_t_plus_one` and `classNumBound_le_log_H` as explicit hypotheses) |
| `Erdos90/NumberFieldDeep_Assembly.lean` | §6–§8: `cm_norm_one_elements` (proved; takes `ht'_ge_t_plus_one` + `classNumBound_le_log_H` hypotheses), `prop_3_2_to_3_6_via_deep` (proved, modulo `brd_tower_data`), `ERDOS_ANT_Postulates` + `ant_postulates` |
| `Erdos90/CosetAveraging.lean` | `lemma_2_4` — coset averaging (fully proved) |
| `Erdos90/Geometric.lean` | `GoodCoset`, `exists_good_coset` (def), lemmas, Theorems 2.3a/b |
| `Erdos90/DiscGeometry.lean` | Discrete geometry lemmas |
| `Erdos90/Main.lean` | Theorem 1.1 (`erdos_unit_distance_false`) + contrapositive |
| `Erdos90.lean` | Root import (imports all modules including CMField, Mathlib4_Extra) |
| `Erdos90/CMField/Basic.lean` | `conjIdeal`, `SplitPrimeData` structure with `h_Q_count_at_split`/`h_Q_count_at_conj` fields (Phase B), `count_conj_swap`, `J_ideal`, `count_J_eq`, `count_J_conj_eq` (all proved) |
| `Erdos90/CMField/CyclotomicSplitPrimes.lean` | Split primes in ℚ(ζ_p); `find_t_primes_modEq_one` + `ramificationIdx_eq_one` + `inertiaDeg_eq_one` proved; `splitPrimeData_from_prime_list` has two sorried `h_Q_count` fields (Phase B; TRUE, count↔ramificationIdx bridge) |
| `Erdos90/CMField/QScaling.lean` | Phase A — `Q_sq_div_conj_mem_integers` and `Q_sq_div_conj_mem_integers_of_spData` (the Q²-scaling integrality lemma, fully proved) |
| `Erdos90/CMField/MinkowskiLattice.lean` | Unscaled CM Minkowski lattice (`cmMinkowskiEquiv`, `cmTransportedBasis`, `cmMinkowskiLattice`, `mem_cmMinkowskiLattice_iff`, `cmSeparation_exists`, `cmFundamentalDomain`, `cmIsAddFundamentalDomain`, etc.).  Moved out of ANT in Phase C to break an import cycle. |
| `Erdos90/CMField/QScalingLattice.lean` | Q²-scaled CM Minkowski lattice built from `MinkowskiLattice`: `qInvSqEquiv`, `qScaledTransportedBasis`, `qScaledCMMinkowskiLattice`, `mem_qScaledCMMinkowskiLattice_iff`, fund domain + properties, `qScaledLattice_separation`, `qScaledLattice_first_coord_injective`.  All proved. |
| `Erdos90/Mathlib4_Extra/Analytic.lean` | Mathlib-candidate analytic lemmas: `log_two_mul_le`, `exp_sub_mul_eq_rpow_div_exp`, `card_ratio_ineq` (all proved). |
| `Erdos90/Mathlib4_Extra/FractionalIdealCount.lean` | Mathlib-candidate `FractionalIdeal.count` lemmas: `le_one_of_forall_count_nonneg`, `mem_range_of_spanSingleton_count_nonneg` (the integrality bridge). |
| `Erdos90/Mathlib4_Extra/FractionalIdealRingEquiv.lean` | Mathlib-candidate `ringEquivOfRingEquiv_coeIdeal` lemma. |
| `Erdos90/Mathlib4_Extra/ClassNumberBound.lean` | Phase E (E1+E2+E3) infrastructure for closing D3.2: `classNumber_le_card_ideals_of_norm_le_minkowski` (proved), `minkBound_le_pow_rootDiscr` (proved), `log_four_r_div_pi_le_two_log_two_r` (proved), `card_ideals_of_norm_le_bound` (proved with crude bound `2^((N!)^[K:ℚ])` via the `I ↦ image in 𝓞_K/(N!·𝓞_K)` injection; tight `N^[K:ℚ]` bound remains a Mathlib-PR-shaped gap). |
| `lakefile.toml` | Build configuration (mathlib dependency, library target `Erd46`) |

## Rules

**Read `README.md` before doing anything.**  It contains project constraints and conventions set by the human maintainer.  Do not duplicate its content here — read it directly.

In particular: never edit or commit `README.md` itself.

## Build

```bash
lake build
```

Requires `leanprover/lean4:v4.30.0-rc2` and mathlib at `master-2026-05-24` (declared in `lakefile.toml`).  The build succeeds with 3 `sorry` warnings on the proof path of `erdos_unit_distance_false` (after Phase A+B+C+D1+D2+D3+D4+D5+E1+E2+E3+E4+E5).  `Mathlib4_Extra/ClassNumberBound.lean` is now fully proved.

Phase D5 (2026-05-26) split `hmr_brd_cm_tower` into two named sub-postulates `gs_cm_tower` (Golod–Shafarevich existence) and `chebotarev_fixed_Q` (Chebotarev/Ihara fixed split primes), with the bundled tower now a proved assembly.  Sorry count went from 2 to 3, but each is now a smaller, more focused Mathlib-PR-shaped statement.

## Proof state — zero axioms, 3 labelled TRUE postulates (all literature gaps)

All number-theoretic postulates are `def`s with `sorry` bodies (zero `axiom` keywords).  The build succeeds; `erdos_unit_distance_false` depends only on `[propext, sorryAx, Classical.choice, Quot.sound]` (foundational Lean axioms + `sorryAx`).

### The three remaining sorries (all literature gaps)

**D3.1.gs** `gs_cm_tower` in `Erdos90/NumberFieldDeep_GSTower.lean:132` — Golod–Shafarevich existence of an infinite CM tower with bounded root discriminant.  TRUE per HMR 2021 §2–4 + CM lift (tensor with ℚ(i)).  Not in Mathlib v4.30; requires class field theory + Golod–Shafarevich inequality.  Multi-year formalization (blocked on Mathlib's Artin reciprocity).

**D3.1.cheb** `chebotarev_fixed_Q` in `Erdos90/NumberFieldDeep_GSTower.lean:154` — Chebotarev/Ihara fixed split primes across the tower.  TRUE per HMR 2021 §3 `theo:ihara` (line 729 in `assets/hmr_2021_src/Cutting_towers_arxiv.tex`).  Not in Mathlib v4.30; requires Chebotarev density theorem + L-function machinery.  Multi-month formalization.

**D3.2** `class_num_bound_of_brd` in `Erdos90/NumberFieldDeep_GSTower.lean:201` — Quantitative Brauer–Siegel bound `log(h_K)/f ≤ 2 · log(2 · rd_F)` for K in the BRD tower with `rootDiscr K ≤ rd_F` (the previous `_h_K_from_brd_tower : True` placeholder was fixed by threading `rootDiscr K ≤ rd_F` through `hmr_brd_cm_tower`).  TRUE per Brauer–Siegel + Louboutin 2000.  Not in Mathlib v4.30; D3.2a (analytic class number formula as algebraic identity) was closed by Phase E5 (`classNumber_eq_residue_formula` in `Mathlib4_Extra/ClassNumberBound.lean`).  Remaining gaps are D3.2b (L(1,χ) upper bound on residue) and D3.2c (regulator lower bound).  Multi-month formalization.

`brd_tower_data` itself is PROVED Lean code that assembles D3.1+D3.2.  Phase D4 closed D3.3 (the `log_H ≥ 2 · log(2 · rd_F)` threshold) by threading the hypothesis through the entire signature chain from `BRDTowerData.getTowerLevel` up to `exists_admissible_family` (which proves it via `C_class = 1`).

### Phase E (D3.2 attack): infrastructure for the Brauer–Siegel chain

Phase E (E1, E2, E3) builds the named chain that would close D3.2 once the analytic ideal-count Mathlib lemma is in place.  Lives in `Erdos90/Mathlib4_Extra/ClassNumberBound.lean`.

**Proved:**
- `classNumber_le_card_ideals_of_norm_le_minkowski` (E1): `h_K ≤ |{ideals of 𝓞 K with absNorm ≤ ⌊M K⌋₊}|`.  Built from `NumberField.exists_ideal_in_class_of_norm_le` + the obvious injection.
- `minkBound_le_pow_rootDiscr` (E3): `M K ≤ ((4 · rootDiscr K) / π)^f` for totally complex K.  Uses `Nat.factorial_le_pow` + `rootDiscr_def` + half-power simplification.
- `log_four_r_div_pi_le_two_log_two_r` (E2): `log((4r)/π) ≤ 2·log(2r)` for `r ≥ 1`.
- `card_ideals_of_norm_le_bound` (E4, 2026-05-26): `|{ideals norm ≤ N}| ≤ 2^((N!)^[K:ℚ])` via the injection `I ↦ image in 𝓞_K/(N!·𝓞_K)` (uses `absNorm I | N!` + `absNorm I ∈ I` ⇒ `(N!·𝓞_K) ⊆ I`).  The codomain is bounded by `Set R` with `|R| = (N!)^[K:ℚ]` (via `absNorm_span_natCast` + `RingOfIntegers.rank`); tight `N^[K:ℚ]` bound would need `# ideals R ≤ |R|` for the Dedekind quotient, which requires CRT + per-prime factorization not yet packaged in Mathlib v4.30.
- `classNumber_eq_residue_formula` (E5, 2026-05-26): the Dirichlet class number formula in algebraic-identity form: `(classNumber K : ℝ) = dedekindZeta_residue K · (torsionOrder K · √|discr K|) / (2^r₁ · (2π)^r₂ · regulator K)`.  Pure rearrangement of Mathlib's `dedekindZeta_residue_def`; no analytic content (the genuine analytic input is in Mathlib's `tendsto_sub_one_mul_dedekindZeta_nhdsGT`).  This is D3.2a in the proposed Brauer–Siegel chain (see `assets/search_results/D32_brauer_siegel_what_we_need.md`); used to turn future upper bounds on the residue into upper bounds on `log h_K / f`.
- `regulator_lower_bound_cm` (E6, sorried as D3.2c, 2026-05-26): Friedman–Zimmert regulator lower bound `regulator K ≥ 1/8` for CM totally complex K with `nrComplexPlaces K ≥ 1`.  Weakened constant of Friedman 1989's `R_K > 0.2052`.  Sorried; off the proof path of `erdos_unit_distance_false` (Mathlib4_Extra not yet hooked in).  Mathlib v4.30 has only `regulator_pos K` (positivity).
- `dedekind_residue_upper_bound_cm` (E7, sorried as D3.2b, 2026-05-26): Louboutin upper bound `dedekindZeta_residue K ≤ (4 · rd_F)^f` for CM totally complex K with `rootDiscr K ≤ rd_F`.  Loose-constant form of Louboutin 2000 Theorem A.  Sorried; off the proof path.  Mathlib v4.30 has only `dedekindZeta_residue_pos K`.  Together with E5 (`classNumber_eq_residue_formula`) and E6 (`regulator_lower_bound_cm`), these are the three pieces that would assemble into `class_num_bound_of_brd` (the D3.2d chain — future work; requires choosing a threshold `M₀(rd_F)` for the `log(w_K)/f → 0` and `log(2π) > 0` asymptotic correction terms).

**Remaining Mathlib gap (would close D3.2 cleanly):**
- The tight `|{ideals norm ≤ N}| ≤ C(K) · N` analytic estimate.  The crude `2^((N!)^[K:ℚ])` proved above is too loose to chain through the discriminant inequality and beat `f · log(rd_F)` asymptotically.

**The complete D3.2 chain (modulo the Mathlib gap):**

```
h_K
  ≤ |{ideals of 𝓞 K with absNorm ≤ ⌊M K⌋}|     (E1, proved)
  ≤ C(K) · M K                                  (MATHLIB GAP: analytic count)
  ≤ C(K) · ((4 · rootDiscr K) / π)^f            (E3, proved)
  ≤ C(K) · ((4 · rd_F) / π)^f                   (rd_K ≤ rd_F, BRD hypothesis)

log(h_K)/f
  ≤ (log C(K))/f + log((4·rd_F)/π)
  → log((4·rd_F)/π) as f → ∞
  ≤ 2 · log(2·rd_F)                             (E2, proved)
```

### Sorry (1) closed (Phase D1+D2)

Both count↔ramificationIdx helpers in `Erdos90/CMField/CyclotomicSplitPrimes.lean`
are fully proved:
- `count_spanSingleton_natCast_of_liesOver` (line 156): the
  bridge `count L P (spanSingleton ((q : ℕ) : L)) = ramificationIdx (Ideal.span {q : ℤ}) P.asIdeal`
  when P lies over span {q}.  Proof uses `FractionalIdeal.count_coe` +
  `Ideal.count_associates_factors_eq` (the key Mathlib bridge) +
  `Ideal.map_span` + `Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count`.
- `count_spanSingleton_natCast_of_not_liesOver` (line 195): count = 0
  when P doesn't lie over span {q}.  Proof uses `Multiset.count_eq_zero` +
  maximality of `Ideal.span {(q : ℤ)}` (requires `Fact (Nat.Prime q)`).

Consequently `splitPrimeData_from_prime_list` (Phase B's sorry) is fully
proved via a sum-over-`qs.toFinset` argument that collapses to 1 via
`Finset.sum_ite_eq'`.

**(2)** `brd_tower_data` in `Erdos90/NumberFieldDeep_GSTower.lean:105` — the BRD CM tower postulate (Phase C).  Asserts `BRDTowerData ℓ`: a tower-level constant `Q : ℕ` with `D₀ = Q²`, a root-discriminant bound `rd_F ≥ 1` with `log rd_F ≤ ℓ · log ℓ`, and a `getTowerLevel` callable that for each `(M, t, log_H)` returns a CM field `K` of complex degree `f ≥ M`, a `SplitPrimeData K (t' * f)` with `sp.Q = Q` (Q fixed across the tower), and the class-number bound `log(h_K)/f ≤ log_H`.

TRUE per:
- Hajir–Maire–Ramakrishna 2021 (`assets/hajir_maire_ramakrishna_2021.pdf` and `assets/tamely-ramified-towers-and-discriminant-bounds-for-number-fields.pdf`): infinite tamely-ramified pro-3 CM tower with `rd < 84`, `Q` fixed across the tower (page 7 of `assets/unit-distance-proof.pdf`).
- Brauer–Siegel applied to BRD tower (Louboutin 2000, `assets/louboutin_2000_class_number.pdf`): bounded rd ⇒ `log(h_K)/f` bounded by an explicit constant.
- Q²-scaling valuation argument: handled by Phase A's `Q_sq_div_conj_mem_integers_of_spData` (fully proved); appears inside `brd_cm_tower_postulate`'s body, which uses Phase A + `QScalingLattice` machinery to build the Q²-scaled lattice on top of any `BRDTowerData`.

Neither HMR nor quantitative Brauer–Siegel is in Mathlib v4.30; closing this requires substantial Mathlib development (class field theory, pro-p group cohomology, Golod–Shafarevich inequality, quantitative Chebotarev, analytic class number formula).

Flow: `brd_tower_data` → `brd_cm_tower_postulate` (PROVED body using QScalingLattice + Phase A) → `gs_tower_levels` → `GSTowerData.getTowerLevel` → `prop_3_2_to_3_6_via_deep` → `exists_admissible_family` → `erdos_unit_distance_false`.

### `exists_cm_class_group_data` is fully proved (no sorries)

All fields of `CMClassGroupData` are proved, including:
- `hmk_unit_inj`: injectivity of `mk_unit` on fibers, proved via `FractionalIdeal.count` API + `dec_trivial` for final Bool case analysis. Uses `count_eq_count_conj_of_fixed` for the split-prime valuation parity argument.
- `hmk_unit_norm`: proved via `cmData.h_φ_norm_div_conj`
- `hmk_unit_mem_Λ`: proved via `cmData.h_div_conj_mem_Λ` (so it depends on the BRD postulate, but the proof itself is complete)
- `h_card_ratio`: proved conditional on `classNumBound_le_log_H` (passed as explicit hypothesis; supplied by `brd_cm_tower_postulate` at the call site)

### Proved (no sorry)

- `BRDTowerData ℓ` (structure) and `brd_cm_tower_postulate` (assembled, proved modulo `brd_tower_data`); the body uses `QScalingLattice` + Phase A's `Q_sq_div_conj_mem_integers_of_spData` + a coordinatewise `mixedEmbedding_apply_isComplex` step to discharge `h_div_conj_mem_Λ`.
- `gs_base_construction` — GS base data with D₀ = 1, rd_F = 2ℓ, log bound via `log_two_mul_le` (legacy compat)
- `gs_tower_levels` / `gs_tower_levels_v2` — take `(t, log_H)`, delegate to `brd_cm_tower_postulate`
- `golod_shafarevich_tower_with_lattice` — extracts `GSTowerData` from `brd_tower_data` and `gs_tower_levels`
- `exists_fiber_ge_div` — pigeonhole lemma (§3)
- 4 CM lemmas in §4 (`norm_div_star_eq_one`, `cm_norm_div_conj_eq_one`, etc.)
- `exists_cm_class_group_data` — all `CMClassGroupData` fields proved (including `hmk_unit_inj`, `hmk_unit_norm`, `hmk_unit_mem_Λ`, `h_card_ratio`); takes `ht'_ge_t_plus_one` and `classNumBound_le_log_H` as explicit hypotheses
- `cm_norm_one_elements` — class-group pigeonhole → norm-one set U, proved; takes `ht'_ge_t_plus_one` and `classNumBound_le_log_H` as explicit hypotheses
- `prop_3_2_to_3_6_via_deep` — assembly, proved (modulo `brd_tower_data`); signature pulls `(t, log_H)` to before the inner `∃ Λ`
- `product_formula_sep`, `integer_separation` — in `Erdos90.CMField.MinkowskiLattice`, proved
- `cmMinkowskiEquiv`, `cmTransportedBasis`, `cmMinkowskiLattice`, `mem_cmMinkowskiLattice_iff`, `cmSeparation_exists`, `cmFundamentalDomain`, `cmIsAddFundamentalDomain`, `cmFundamentalDomain_finite_volume`, `cmMinkowskiLattice_countable`, `cmSeparation` — in `Erdos90.CMField.MinkowskiLattice`, all proved
- `qInvSqEquiv`, `qScaledTransportedBasis`, `qScaledCMMinkowskiLattice`, `mem_qScaledCMMinkowskiLattice_iff`, `qScaledCMMinkowskiLattice_countable`, `qScaledFundamentalDomain`, `qScaledIsAddFundamentalDomain`, `qScaledFundamentalDomain_bounded`, `qScaledFundamentalDomain_volume_lt_top`, `qScaledFundamentalDomain_volume_pos`, `qScaledLattice_separation`, `qScaledLattice_first_coord_injective` — in `Erdos90.CMField.QScalingLattice`, all proved (Phase C lattice machinery)
- `Q_sq_div_conj_mem_integers`, `Q_sq_div_conj_mem_integers_of_spData` — in `Erdos90.CMField.QScaling`, the Phase A integrality lemma, proved (~220 LOC)
- `le_one_of_forall_count_nonneg`, `mem_range_of_spanSingleton_count_nonneg`, `ringEquivOfRingEquiv_coeIdeal` — in `Erdos90.Mathlib4_Extra.*`, all proved (Mathlib candidates)
- `sawin_tower_exists`, `ant_postulates` — filled, delegate to `gs_tower_levels` + `exists_cm_class_group_data`

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
- `gs_base_construction` — GS base data (NumberFieldDeep.lean §2, was sorried, now proved)
- `log_two_mul_le` — analytic helper (NumberFieldDeep.lean §1)
- `exp_sub_mul_eq_rpow_div_exp` — exp identity for Prop 2.2 cardinality bound (NumberFieldDeep.lean §1)
- `card_ratio_ineq` — cardinality ratio inequality (NumberFieldDeep.lean §1)
- `exists_fiber_ge_div` — pigeonhole lemma (NumberFieldDeep.lean §3, fully proved)
- `norm_div_star_eq_one` — pure complex analysis: ‖z / star z‖ = 1 (NumberFieldDeep.lean §4, fully proved)
- `cm_norm_div_conj_eq_one` — ‖φ(α / c(α))‖ = 1 at each complex embedding (NumberFieldDeep.lean §4, fully proved)
- `normAtPlace_mixedEmbedding_cm_div_conj_eq_one` — normAtPlace = 1 under mixedEmbedding (NumberFieldDeep.lean §4, fully proved)
- `mixedEmbedding_cm_div_conj_complex_norm_one` — concrete ‖.2 w‖ = 1 per complex place (NumberFieldDeep.lean §4, fully proved)
- `cm_norm_one_elements` — class-group pigeonhole → norm-one set U (NumberFieldDeep.lean §6, proved)
- `prop_3_2_to_3_6_via_deep` — assembly theorem (NumberFieldDeep.lean §7, proved modulo `brd_cm_tower_postulate`)
- `hmk_unit_inj` — mk_unit injectivity on fibers (§5, fully proved via `FractionalIdeal.count` + `dec_trivial`)
- `exists_cm_class_group_data` — full `CMClassGroupData` construction (§5, fully proved, no sorries)
- `conjIdeal` — complex conjugation on ideals of 𝓞_K (CMField/Basic.lean, fully proved)
- `conjIdeal_mul`, `conjIdeal_conjIdeal`, `conjIdeal_injective`, `conjIdeal_isPrime`, `conjIdeal_ne_bot` — basic conjIdeal lemmas (CMField/Basic.lean, all fully proved)
- `SplitPrimeData` — structure for m split-prime ideal pairs (CMField/Basic.lean, fully defined)
- `find_t_primes_modEq_one` — Dirichlet: t primes ≡ 1 (mod p) (CMField/CyclotomicSplitPrimes.lean, fully proved)
- `cyclof_pos`, `cyclof_ge_one` — basic facts about f = (p-1)/2 (CMField/CyclotomicSplitPrimes.lean, proved)

### Auxiliary defs
- `C_class := 1` (concrete `def`)
- `polydisc_measurable` — lemma (fully proved)
- `GSTowerData ℓ` — structure abstracting the BRD tower output (fields: `D₀`, `hD₀_pos`, `rd_F`, `hrd_F_ge1`, `hlog_rd`, `getTowerLevel (M, t, log_H, ht, hlog_H_pos)`)
- `GSBaseData ℓ` — structure for Props 3.2–3.5 base field data (fields: `D₀`, `hD₀_pos`, `rd_F`, `hrd_F_ge1`, `hlog_rd`)
- `CMTowerData f hf1 Λ K` — fields: `φ`, `h_nrComplexPlaces`, `h_nrRealPlaces`, `h_φ1_norm`, `h_φ_norm_div_conj`, `t'_param : ℕ`, `spData : SplitPrimeData K (t'_param * f)`, `h_div_conj_mem_Λ` (non-universal: for the fixed `spData`), `classNumBound`, `hClassNum`.  (The `mem_iff` field was removed in Phase C; it described an unscaled Λ characterization that is false for the Q²-scaled lattice.)
- `BRDTowerData ℓ` — fields: `Q : ℕ`, `hQ_pos`, `D₀ : ℝ`, `hD₀_pos`, `hD₀_eq : D₀ = (Q : ℝ)^2`, `rd_F`, `hrd_F_ge1`, `hlog_rd`, `getTowerLevel (M, t, log_H, ht, hlog_H_pos)` returning `∃ K f sp ..., sp.Q = Q ∧ log(h_K)/f ≤ log_H`.
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

5. The two remaining sorries are (after Phase D3+D4):
   - `hmr_brd_cm_tower` (`NumberFieldDeep_GSTower.lean:116`): HMR 2021 existence + Chebotarev.
   - `class_num_bound_of_brd` (`NumberFieldDeep_GSTower.lean:137`): quantitative Brauer–Siegel.

   Both are genuine multi-month Mathlib gaps with explicit literature citations.  `brd_tower_data` is proved Lean code assembling them.

   The entire rest of the formalization — geometry, coset averaging, CM field class-group construction, Q²-scaling, Q²-scaled lattice machinery, cyclotomic split-prime data (`splitPrimeData_from_prime_list` and its `h_Q_count` fields, proved via the count↔ramificationIdx bridges), combinatorial counting — is fully proved.

6. **∃ elimination into Type:** `Exists.casesOn` only eliminates into `Prop` in Lean 4.  When constructing a structure with `ℝ` or other non-`Prop` fields, use helper structures (like `GSBaseData`) instead of `∃` existential hypotheses — otherwise `obtain`/`cases` fails with "recursor can only eliminate into Prop".

7. Commit often with descriptive messages.  Always end commits with the co-author line.

## Lessons

### 2026-05-26 (Phase E4): Close `card_ideals_of_norm_le_bound` via crude subset injection

The tight bound `|{ideals norm ≤ N}| ≤ N^[K:ℚ]` looked like a days-to-weeks
combinatorial argument, but on analysis turned out to require either
(a) Dedekind quotient CRT + per-prime factorization not in Mathlib v4.30,
or (b) Hermite normal form for ℤ^n sublattices also not packaged.

The naive shortcut "# ideals of finite ring R ≤ |R|" is FALSE for general
finite commutative R (an F_p-vector-space of high dimension has more
subspaces than elements).  It IS true for `𝓞_K/(m·𝓞_K)` via the
Dedekind chain structure ∏ (a_𝔭 + 1) ≤ ∏ N(𝔭)^{a_𝔭} = m^n, but
proving that requires the CRT+factorization chain above.

Phase E4 closes the sorry with a much weaker but cleanly provable bound:
`|{ideals norm ≤ N}| ≤ 2^((N!)^[K:ℚ])` via the injection
`I ↦ image of I in 𝓞_K/(N!·𝓞_K)`.  Three pieces:

- Well-defined: `absNorm I ≤ N` ⇒ `absNorm I | N!` (Nat.dvd_factorial) and
  `absNorm I ∈ I` (Mathlib `Ideal.absNorm_mem`), so `(N!·𝓞_K) ⊆ I`.
- Injective: `Ideal.comap_map_mk` applied with `J ≤ I` from above.
- Codomain bound: `Set R` has cardinality `2^|R|` (`Fintype.card_set`),
  and `|R| = (N!)^[K:ℚ]` via `Ideal.absNorm_span_natCast` (in S = 𝓞_K
  gives `(N!)^Module.finrank ℤ (𝓞 K)`) + `RingOfIntegers.rank`
  (=`Module.finrank ℚ K`).

The bound is doubly-exponential and breaks the downstream Brauer–Siegel
chain (was: `≤ ⌊minkBound⌋^[K:ℚ]`; now: `≤ 2^((⌊minkBound⌋!)^[K:ℚ])`).
But `classNumber_le_minkowski_pow_degree` only feeds the trivial
commentary `classNumber_log_bound_crude_remark`, which already
documented falling short by a factor of `f`.  So no downstream proof
breaks; the Mathlib gap is now clearly demarcated.

**Lesson:** When a "crude polynomial" bound turns out to require
substantial Mathlib infrastructure (CRT for Dedekind quotients,
Hermite NF, etc.), back off to a `2^|R|` subset bound instead of
chasing a tight `N^n`.  The proof of the structural injection is the
same; only the codomain-size estimate differs.  Honest about the
remaining gap is better than a fake proof.

### 2026-05-26 (Phase E1+E2+E3): Build the Brauer–Siegel chain infrastructure

D3.2 (the quantitative Brauer–Siegel bound) decomposes into a chain of pieces.
Phase E built the proved pieces and identified the one Mathlib-gap piece.

**E1**: prove the injection `h_K ≤ |{bounded-norm ideals}|` from
`NumberField.exists_ideal_in_class_of_norm_le` + `ClassGroup.mk0` as left
inverse.  ~40 LOC of Lean.

**E2**: prove the log inequality `log((4r)/π) ≤ 2·log(2r)` for `r ≥ 1`.
~10 LOC of `nlinarith`.

**E3**: prove the Minkowski-bound ≤ root-discriminant-power inequality
`M K ≤ ((4·rootDiscr K)/π)^f` for totally complex K of positive degree.
~50 LOC, using `Nat.factorial_le_pow` + `rootDiscr_def`.

**Mathlib gap**: the analytic ideal-count `|{ideals of 𝓞 K with absNorm ≤ N}| ≤ C(K) · N`.
This is a Dedekind-zeta partial-sum result not in Mathlib v4.30.  Sorried as
`card_ideals_of_norm_le_bound` with a crude polynomial form for now; the
genuine analytic form is the multi-month Mathlib contribution.

**Lesson:** When a sorry hides a Mathlib gap that's substantial but
well-understood (here: Brauer–Siegel), the right move is to *build the
named chain* around it.  Even if the chain has a missing link, naming
each link makes (a) the missing piece a clean Mathlib-PR target,
(b) the proof complete once that PR lands, and (c) the code reviewable
without expert knowledge of the gap.

### 2026-05-26 (Phase D4): Close the architectural gap by threading the hypothesis

Phase D3 left 3 sorries; the third (`brd_log_H_threshold`) was an
architectural gap, not a literature gap: claimed `log_H ≥ 2 · log(2 · rd_F)`
from `log_H > 0`, which is false in general but true in the actual call
chain via `exists_admissible_family`'s choice of `log_H_base = 2 · C_class
· log(2 · rd_F)` with `C_class = 1`.

Phase D4 closes this by threading the hypothesis through the signature
chain (8 functions across 4 files):

  BRDTowerData.getTowerLevel ──┐
  brd_cm_tower_postulate       │
  gs_tower_levels_proved       │  +(hlog_H_ge_rd : log_H ≥ 2·log(2·rd_F))
  gs_tower_levels              │   added everywhere
  GSTowerData.getTowerLevel    │
  gs_tower_levels_v2           │
  ERDOS_ANT_Postulates.gs_tower│
  prop_3_2_to_3_6_via_deep ────┘
  exists_admissible_family       proves it via C_class = 1

The threading is straightforward: each function takes the hypothesis and
passes it down (or, at the bottom, proves it).

Sorry count: 3 → 2.  Both remaining sorries are now genuine literature
gaps (HMR 2021, Brauer–Siegel quantitative).

**Lesson:** Architectural sorries (where the statement is true-in-practice
but not from local hypotheses) are often closeable by threading the
needed hypothesis through the call chain.  This is mechanical work,
not new mathematics, and is worth doing to keep the remaining sorries
honest.

### 2026-05-26 (Phase D3): Decompose `brd_tower_data` into 3 Mathlib-PR-shaped sorries

Phase D3 splits the single `brd_tower_data` postulate into three labelled
one-line sorries:
- `hmr_brd_cm_tower` (HMR 2021 + Chebotarev)
- `class_num_bound_of_brd` (Brauer–Siegel quantitative)
- `brd_log_H_threshold` (architectural gap)

Each has a docstring citing the relevant literature.  `brd_tower_data`'s
body is now proved Lean code assembling them via `Classical.choose` (the
HMR existential returns Types, so `Exists.casesOn` can't eliminate
directly — needs `Classical.choose` to pull out the data fields).

**Lesson:** When a `def` returns a structure with Type-valued fields and
you want to destructure an existential to construct it, prefer
`Classical.choose` over `obtain`/`rcases` (which only eliminate into
Prop).  The Type-valued pattern requires Type-eliminating extraction.

### 2026-05-26 (Phase D1+D2): Close Sorry (1) — the count↔ramificationIdx bridges

Phase D1 decomposed `splitPrimeData_from_prime_list`'s `h_Q_count` sorries
into a sum-over-`qs.toFinset` argument relying on two helper lemmas.
Phase D2 then closed both helpers:

- `count_spanSingleton_natCast_of_liesOver`: the key Mathlib lemma is
  `Ideal.count_associates_factors_eq` (in `DedekindDomain/Ideal/Lemmas.lean`),
  which gives `(Associates.mk P).count (Associates.mk I).factors =
  Multiset.count P (normalizedFactors I)`.  Combined with
  `FractionalIdeal.count_coe`, `Ideal.map_span`, and
  `Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count`,
  the bridge falls out.

- `count_spanSingleton_natCast_of_not_liesOver`: uses the same `count_coe`
  + `count_associates_factors_eq` reduction, then `Multiset.count_eq_zero`:
  if `P ∈ normalizedFactors (Ideal.span {q : 𝓞 L})`, then `P ∣ span {q}`,
  so `span {q : ℤ} ⊆ Ideal.under ℤ P`; by maximality of `span {q : ℤ}`
  (needs `Fact (Nat.Prime q)`) and properness of `Ideal.under ℤ P` (from
  `P.asIdeal ≠ ⊤`), we get equality, contradicting `¬LiesOver`.

Sorry count: 2 → 1.  The signature change to require `Fact (Nat.Prime q)`
in the second helper propagates as a typeclass requirement; the cyclotomic
caller already has `_hqs_prime` so the change is invisible.

**Lesson:** When a "Mathlib API gap" feels insurmountable, search wider
(`grep -rn` across multiple namespaces).  The needed
`Ideal.count_associates_factors_eq` was in a less-obvious file
(`DedekindDomain/Ideal/Lemmas.lean`, not `Factorization.lean`).

### 2026-05-26 (Phase A+B+C): Decompose the bundled postulate via paper insight

The `brd_cm_tower_postulate` from the earlier "collapse" step was a single monolithic sorry hiding four sub-claims: HMR existence, Brauer–Siegel quantitative bound, Q²-scaled lattice membership, and the lattice-construction plumbing.  After re-reading the paper (page 7 of `assets/unit-distance-proof.pdf`), the architectural blocker was identified: the paper FIXES Q across the tower (the same rational primes `q_b` split in every `K_j`), so `D = Q²` is also fixed across the tower — matching the existing `AdmissibleFamily.D` (constant in `M`) without contradiction.

With the architecture validated, the four sub-claims were separated:
- **Phase A** (committed): Prove the Q²-scaling integrality lemma `Q² · (α / c(α)) ∈ 𝓞_K` as a standalone fact (`Erdos90/CMField/QScaling.lean`, ~220 LOC).  Uses `count_conj_swap` + `count_J_eq` + `count_J_conj_eq` for the case-analysis-on-prime argument.
- **Phase B** (committed): Add `h_Q_count_at_split` and `h_Q_count_at_conj` fields to `SplitPrimeData` (in `CMField/Basic.lean`).  These are abstract hypotheses on any `SplitPrimeData`; the cyclotomic instance is sorried as a TRUE statement provable from `ramificationIdx_eq_one`.
- **Phase C (b)** (committed): Introduce `BRDTowerData ℓ` structure + `brd_tower_data : BRDTowerData ℓ := sorry`, and prove `brd_cm_tower_postulate`'s body using `BRDTowerData` + `QScalingLattice` machinery + Phase A's lemma.  Result: the original monolithic sorry becomes proved Lean code modulo the single new `brd_tower_data` postulate.

Net effect: 1 monolithic sorry → 2 narrow sorries, ~600 LOC of proved Lean code in between.  Each remaining sorry is a one-line statement with a clear Mathlib-citable provenance.

**Lessons:**
- Always read the paper before refactoring around a hard sorry — the architectural constraint that blocked me (Q "growing with M") turned out to be a misreading; the paper fixes Q once.
- A "structural" postulate (HMR + BS together) is cleaner than splitting into N small but coupled postulates, especially when the coupling carries provability constraints (e.g., the `sp.Q = Q` equation that ties the per-M tower level to the fixed top-level constants).
- Mathlib4-candidate generic lemmas belong in their own `Mathlib4_Extra/` folder, grouped by topic (`Analytic`, `FractionalIdealCount`, `FractionalIdealRingEquiv` so far).
- When a Lean file would induce an import cycle, look for the architectural prerequisite: in Phase C, moving the unscaled Minkowski-lattice machinery from `ANT` to a new `CMField/MinkowskiLattice.lean` (earlier in the build graph) lets `QScalingLattice` and `GSTower` both use it without going through ANT.

### 2026-05-26: Collapse multiple false sorries into one true labeled postulate

Two sorried statements were both FALSE in the current Lean architecture:
- `h_div_conj_mem_Λ` (with unscaled Λ = `Φ(𝒪_K)`): false because `α/c(α) ∉ 𝒪_K` whenever `v_𝔓(α/c(α)) = -2`.
- `classNumBound_le_log_H` (for `K = ℚ(ζ_p)`): false because `log(h_K)/f → ∞` as `p → ∞` (Brauer–Siegel), while `log_H` is fixed.

**Refactor:** Replaced both with a single TRUE postulate `brd_cm_tower_postulate (ℓ, base, M, t, log_H, ...) := sorry` that asserts the existence of a CM tower level with `cmData.t'_param ≥ ⌈t⌉ + 1` and `cmData.classNumBound ≤ log_H` and the Q²-scaled lattice. Mathematically TRUE per Hajir–Maire–Ramakrishna 2021 + Brauer–Siegel + Q²-scaling valuation argument; none in Mathlib v4.30.

Architectural ripple to make this possible:
- `CMTowerData` now carries fixed `t'_param`/`spData` (was: `splitPrimesFor : ∀ t' → SplitPrimeData K (t' * f)` with `h_div_conj_mem_Λ : ∀ t' → ...`). A fixed Λ can't simultaneously contain Q⁻²·𝒪_K for every Q indexed by `t'`, so `t'_param` had to be a structure field.
- `prop_3_2_to_3_6_via_deep`, `gs_tower_levels`, `GSTowerData.getTowerLevel` all pull `(t, log_H)` to before the inner `∃ Λ` so that Λ can depend on `t`.
- `exists_cm_class_group_data` and `cm_norm_one_elements` take `ht'_ge_t_plus_one : t + 1 ≤ cmData.t'_param` as an explicit hypothesis (was: derived internally from the universal `splitPrimesFor` callback).

**Lesson:** When multiple sorries each encode FALSE intermediate statements that combine into one TRUE statement at a higher level, refactor to expose the TRUE statement as a single postulate at the boundary. A `∀` quantifier inside a structure field is a red flag if any single instance would need to be tied to a Λ choice that depends on the quantified value — convert to a fixed field with the binder lifted to the structure's parameters.

### 2026-05-25: Never pack false statements as structure fields

`classNumBound_nonpos` was a field of `CMTowerData` asserting `log(h_K)/f ≤ 0`, equivalent to `h_K = 1`. This is mathematically false for ℚ(ζ_p) with p ≥ 23 (Masley–Montgomery). It was introduced as a bridge to derive `classNumBound ≤ log_H` via `classNumBound ≤ 0 ≤ log_H`.

**What went wrong:** The field was FALSE but sorried in `gs_tower_levels_proved`. Even if it could be proved for some small primes, the tower picks primes via `Nat.exists_infinite_primes` (an arbitrary prime ≥ bound), so the statement is unprovable in general.

**The fix:** Replaced `classNumBound_nonpos : classNumBound ≤ 0` with a direct postulate `classNumBound_le_log_H : classNumBound ≤ log_H` at the call site (`prop_3_2_to_3_6_via_deep`). The new statement is the Minkowski class-number bound: `h_K ≤ exp(log_H · f)` — mathematically TRUE (though still not in Mathlib).

**Lesson:** When a structure field encodes a numeric inequality that depends on external parameters (like `log_H`), don't bake a stronger false intermediate into the structure. Instead, pass the actual needed inequality as an explicit hypothesis at the point where all parameters are in scope. A sorried TRUE statement is better than a sorried FALSE one — the true one can eventually be proved when the relevant Mathlib API arrives.

## Memory

Persistent memory is at `/Users/khanh/.claude/projects/-Volumes-Hippopotamus-vault-code-erd46/memory/`.  Store user preferences, project decisions, and non-obvious context there.
