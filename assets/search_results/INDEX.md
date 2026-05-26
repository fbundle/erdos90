# Research index — assets for closing the 4 remaining sorries

The Lean formalization (`Erdos90/`) has **4 remaining sorries**, all literature gaps.
This directory organizes the external research material we depend on.

## Current sorries (as of 2026-05-27)

| # | Sorry | Location | Status |
|---|---|---|---|
| 1 | `gs_cm_tower` | `NumberFieldDeep_GSTower.lean:133` | proof path — needs Mathlib class field theory |
| 2 | `chebotarev_fixed_Q` | `NumberFieldDeep_GSTower.lean:185` | proof path — needs Mathlib Chebotarev / L-functions |
| 3 | `regulator_lower_bound_cm` | `Mathlib4_Extra/ClassNumberBound.lean:296` | off-path — needs Mathlib L-function FE + Friedman |
| 4 | `dedekind_residue_upper_bound_cm` | `Mathlib4_Extra/ClassNumberBound.lean:332` | off-path — needs Mathlib L-function FE + Louboutin |

Sorries 3 and 4 share the same Mathlib gap: the functional equation for `dedekindZeta`.

## Strategic documents

- **`closing_roadmap.md`** — 5-PR incremental Mathlib strategy to close the
  off-path sorries (sorries 3 + 4).  Identifies the shared `dedekindZeta`
  functional equation as the key shared infrastructure.
- **`mathlib_lseries_infrastructure.md`** — survey of Mathlib v4.30's existing
  L-series infrastructure (substantial: AbstractFuncEq, Dirichlet L-functions
  with FE, Hurwitz/Riemann zeta).  Identifies the precise gap.

## Per-sorry notes

### Sorries 1 + 2 (D3.1.gs + D3.1.cheb): HMR BRD CM tower + Chebotarev
- `D31_hmr_brd_what_we_need.md` — mathematical statement + Lean decomposition
- `D31_class_field_theory_mathlib_gap.md` — Mathlib survey (Artin reciprocity absent)
- `hmr_2021_key_theorems.md` — line-referenced HMR 2021 extracts (`theo:ihara`)

### Sorries 3 + 4 (D3.2c + D3.2b): Brauer–Siegel + analytic class number
- `D32_brauer_siegel_what_we_need.md` — explicit `log(h_K)/f ≤ 2·log(2·rd_F)` chain
- `D32_analytic_class_number_mathlib_gap.md` — Mathlib-side analysis
- `class_number_bound_derivation.md` — cyclotomic-case derivation

## Source papers (full text / tex)

### On the proof path
- `assets/arXiv-2605.20579v1.pdf` + `assets/sawin_src/` — Sawin 2026, *"Erdős unit-distance lower bound"*
- `assets/arXiv-2605.20695v1.pdf` + `assets/remarks_src/` — Gowers–Sawin–Alon–Wood 2026, *"Remarks"*
- `assets/unit-distance-proof.pdf` — OpenAI extended unit distance paper
- `assets/unit-distance-cot.pdf` — OpenAI chain of thought

### For D3.1 (HMR / GS / Chebotarev)
- `assets/hajir_maire_ramakrishna_2021.pdf` + `assets/hmr_2021_src/Cutting_towers_arxiv.tex` — **HMR 2021**, arXiv:1901.04354.  Contains `theo:ihara` (key).
- `assets/hajir_maire_cutting_2021.pdf` — Hajir–Maire 2021
- `assets/tamely-ramified-towers-and-discriminant-bounds-for-number-fields.pdf`
- `assets/ellenberg_venkatesh_2007.pdf` — class number bounds
- `assets/ershov_gs_survey.pdf` — GS groups survey
- `assets/zhou_gs_thesis.pdf` — GS thesis
- `assets/milne_cm_notes.pdf` — CM field background

### For D3.2 (Brauer–Siegel / Louboutin / L-functions)
- `assets/louboutin_2000_class_number.pdf` — **Louboutin 2000**, the source of the residue upper bound
- `assets/arXiv-2507.10387v1.pdf` + `assets/akhtari_vaaler_widmer_src/` — AVW 2025, effective CM equidistribution

## Mathlib quick references (proved infrastructure used by this project)

- `mathlib_gs_chebotarev_api.md` — Galois + Frobenius API
- `mathlib_class_number.md`, `mathlib_discriminant.md` — class group / discriminant
- `mathlib_canonical_embedding.md` — Minkowski embedding
- `mathlib_cyclotomic_basic.md`, `mathlib_cyclotomic_instances.md` — cyclotomic fields
- `mathlib_cm_field.md` — CM field machinery
- `mathlib_nf_norm.md`, `mathlib_nf_units.md`, `mathlib_norm_bound.md` — norms / units
- `mathlib_dedekind_ideal.md`, `mathlib_valuation_api.md` — Dedekind ideals
- `minkowski_bound_api.md` — Minkowski bound usage
- `mathlib_api_audit.md` — broad API survey

## Wikipedia / background

- `wikipedia_golod_shafarevich.md`, `wikipedia_class_field_tower.md`
- `wikipedia_cm_field.md`, `wikipedia_algebraic_norm.md`
- `web_search_ant_references.md` — broader web search

## Paper extracts (background)

- `sawin_lemmas_6_9.md`, `sawin_section2_construction.md` — Sawin paper extracts
- `openai_paper_prop2_2_construction.md`, `openai_paper_references.md`
- `paper_answers_to_ai_questions.md`
- `sawin_2605_20579_*.md`, `remarks_2605_20695_*.md`, `akhtari_vaaler_widmer_*.md`,
  `hajir_maire_ramakrishna_*.md`, `ellenberg_venkatesh_*.md` (abstract / fulltext / html)

## Recommended reading order

### For the off-path analytic sorries (3 + 4, more accessible)
1. `closing_roadmap.md` — the 5-PR strategy
2. `mathlib_lseries_infrastructure.md` — what Mathlib already has
3. `D32_brauer_siegel_what_we_need.md` — the chain we use
4. `D32_analytic_class_number_mathlib_gap.md` — Mathlib gaps
5. `louboutin_2000_class_number.pdf` §1–3 — the explicit bound

### For the proof-path sorries (1 + 2, harder)
1. `D31_hmr_brd_what_we_need.md` — the decomposition
2. `hmr_2021_key_theorems.md` — locate `theo:ihara` in the source tex
3. `D31_class_field_theory_mathlib_gap.md` — set realistic expectations
4. `hmr_2021_src/Cutting_towers_arxiv.tex` §2–4 — the proof structure

## State summary

`erdos_unit_distance_false` is proved modulo the 4 sorries above.  All depend
on Mathlib analytic NT / class field theory infrastructure that doesn't yet
exist.  The geometric + combinatorial + CM-field-class-group + lattice
infrastructure (everything else) is fully proved.

See `closing_roadmap.md` for the concrete Mathlib PR-shaped strategy.
