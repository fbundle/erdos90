# Research index — assets for closing the 2 remaining sorries

The Lean formalization (`Erdos90/`) has **two remaining sorries** on the proof path of
`erdos_unit_distance_false`, both literature gaps. This directory organizes the
external research material we depend on.

## The two sorries

| Sorry | Location | Depends on |
|---|---|---|
| **D3.1** `hmr_brd_cm_tower` | `Erdos90/NumberFieldDeep_GSTower.lean:116` | HMR 2021 + Chebotarev + CM lift |
| **D3.2** `class_num_bound_of_brd` | `Erdos90/NumberFieldDeep_GSTower.lean:137` | Brauer–Siegel + Louboutin + L(1,χ) bound |

## How this directory is organized

### D3.1 — HMR BRD CM tower + Chebotarev
- `D31_hmr_brd_what_we_need.md` — exact mathematical theorem we depend on, plus
  recommended Lean signature decomposition (4 named sub-pieces)
- `D31_class_field_theory_mathlib_gap.md` — Mathlib v4.30 survey: what exists, what's
  missing, realistic timeline (12–24 months for Artin reciprocity in Mathlib)
- `hmr_2021_key_theorems.md` — line-referenced extract from HMR 2021 tex, identifying
  `theo:ihara` (line 729) as the key existence theorem

### D3.2 — Brauer–Siegel + analytic class number
- `D32_brauer_siegel_what_we_need.md` — the explicit `log(h_K)/f ≤ 2·log(2·rd_F)`
  bound; **flags the `_h_K_from_brd_tower : True` placeholder bug** in the current
  Lean statement (1-line fix needed)
- `D32_analytic_class_number_mathlib_gap.md` — Mathlib survey:
  `dedekindZetaResidue` + Dirichlet limit form exist; L(1,χ) bound + functional
  equation + regulator lower bound missing
- `class_number_bound_derivation.md` — earlier derivation notes (cyclotomic case)

### Source papers (full text / tex)

**On the proof path:**
- `assets/arXiv-2605.20579v1.pdf` + `assets/sawin_src/` — Sawin, *"Erdős unit-distance
  lower bound"* (2026) — main paper being formalized
- `assets/arXiv-2605.20695v1.pdf` + `assets/remarks_src/` — Gowers–Sawin–Alon–Wood,
  *"Remarks on the disproof…"* (2026) — companion paper
- `assets/unit-distance-proof.pdf` — OpenAI extended unit distance paper

**For D3.1 (HMR / GS / Chebotarev):**
- `assets/hajir_maire_ramakrishna_2021.pdf` + `assets/hmr_2021_src/` — HMR 2021,
  *"Cutting towers of number fields"* (arXiv:1901.04354). **Contains `theo:ihara`**
- `assets/hajir_maire_cutting_2021.pdf` — Hajir–Maire 2021, related companion
- `assets/tamely-ramified-towers-and-discriminant-bounds-for-number-fields.pdf` —
  tame ramification version of the GS tower
- `assets/ellenberg_venkatesh_2007.pdf` — Ellenberg–Venkatesh 2007, related class
  number bounds
- `assets/ershov_gs_survey.pdf` — Ershov, *"Golod–Shafarevich groups: a survey"*
- `assets/zhou_gs_thesis.pdf` — Zhou thesis on Golod–Shafarevich
- `assets/milne_cm_notes.pdf` — Milne CM notes (background)

**For D3.2 (Brauer–Siegel / Louboutin / L-functions):**
- `assets/louboutin_2000_class_number.pdf` — **Louboutin 2000**, *"Explicit upper
  bounds for residues of Dedekind zeta functions and class numbers of CM-fields"*.
  Source of the explicit `log(h_K)/f ≤ 2·log(2·rd_F)` bound
- `assets/arXiv-2507.10387v1.pdf` + `assets/akhtari_vaaler_widmer_src/` —
  Akhtari–Vaaler–Widmer, *"Effective equidistribution of norm one elements in
  CM-fields"* (2025). Effective constants for CM fields.

### Wikipedia / Mathlib quick references

- `wikipedia_golod_shafarevich.md`, `wikipedia_class_field_tower.md`,
  `wikipedia_cm_field.md`, `wikipedia_algebraic_norm.md`
- `mathlib_gs_chebotarev_api.md`, `mathlib_class_number.md`,
  `mathlib_discriminant.md`, `mathlib_canonical_embedding.md`,
  `mathlib_cyclotomic_basic.md`, `mathlib_cyclotomic_instances.md`,
  `mathlib_cm_field.md`, `mathlib_nf_norm.md`, `mathlib_nf_units.md`,
  `mathlib_norm_bound.md`, `mathlib_dedekind_ideal.md`, `minkowski_bound_api.md`,
  `mathlib_valuation_api.md`, `mathlib_api_audit.md`

### Other paper extracts (background)

- `sawin_lemmas_6_9.md`, `sawin_section2_construction.md`,
  `openai_paper_prop2_2_construction.md`, `openai_paper_references.md`,
  `paper_answers_to_ai_questions.md`
- `sawin_2605_20579_abstract.md` / `_fulltext.md` / `_html_full.md`
- `remarks_2605_20695_abstract.md` / `_fulltext.md` / `_html_full.md`
- `akhtari_vaaler_widmer_abstract.md` / `_fulltext.md` / `_html_full.md`
- `hajir_maire_ramakrishna_abstract.md` / `_html.md`
- `ellenberg_venkatesh_abstract.md` / `_html.md`
- `web_search_ant_references.md` — broader web search results

## Recommended reading order for someone closing the sorries

### To attempt D3.2 first (lower bar, more accessible):
1. `D32_brauer_siegel_what_we_need.md` — understand the target bound + the `True`
   placeholder bug
2. `D32_analytic_class_number_mathlib_gap.md` — see what Mathlib already has
3. `louboutin_2000_class_number.pdf` §1–3 — explicit residue bounds
4. Skim `vendor/mathlib4/Mathlib/NumberTheory/NumberField/DedekindZeta.lean` and
   `Ideal/Asymptotics.lean` — pre-built infrastructure

### To attempt D3.1 (harder, requires Mathlib-level CFT effort):
1. `D31_hmr_brd_what_we_need.md` — read the decomposition into 4 pieces
2. `hmr_2021_key_theorems.md` — locate `theo:ihara` in the source tex
3. `D31_class_field_theory_mathlib_gap.md` — set realistic expectations
4. `hmr_2021_src/Cutting_towers_arxiv.tex` §2–4 (lines 391–1330) — read the proof
   sketch carefully

## Honest timeline

- **D3.2**: 6–12 months focused Mathlib effort (analytic class number formula
  unfolding is plausibly 1–2 weeks; L(1,χ) bounds and regulator lower bounds are
  the real work).
- **D3.1**: 24–36 months. Blocked on Mathlib having Artin reciprocity (class field
  theory). Not closeable in isolation.

See per-sorry notes for details.
