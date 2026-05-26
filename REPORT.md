# REPORT — Erd46 formalization status

This file is the **human-readable progress log** for the project.  Written by the AI agent; intended for the human maintainer to skim and track.  Distinct from:
- `CLAUDE.md` — agent instructions
- `README.md` — human-maintained project description

## Current state (last updated: 2026-05-27 evening session)

`erdos_unit_distance_false` (Theorem 1.1) is fully formalized **modulo 4 named sorries**, each cited with literature and decomposed into Mathlib-PR-shaped pieces.  The proof depends only on standard foundational axioms (`propext`, `sorryAx`, `Classical.choice`, `Quot.sound`) — no custom axioms.

### The 4 sorries

| # | Name | Location | Type | Mathlib gap |
|---|---|---|---|---|
| 1 | `gs_cm_tower` | `Erdos90/NumberFieldDeep_GSTower.lean:133` | proof path | class field theory + Golod–Shafarevich + pro-p cohomology (multi-year) |
| 2 | `chebotarev_fixed_Q` | `Erdos90/NumberFieldDeep_GSTower.lean:185` | proof path | Chebotarev density theorem + L-function continuation (multi-month) |
| 3 | `regulator_lower_bound_cm` | `Erdos90/Mathlib4_Extra/ClassNumberBound.lean:296` | off-path | Friedman 1989: analytic regulator formula via Mellin transforms |
| 4 | `dedekind_residue_upper_bound_cm` | `Erdos90/Mathlib4_Extra/ClassNumberBound.lean:332` | off-path | Louboutin 2000: functional equation of ζ_K + L(1,χ) bounds |

### Recently closed (this session, 2026-05-26 → 2026-05-27)

- `class_num_bound_of_brd` — proof-path sorry, now proved via D3.2d chain assembly combining E5+D3.2b+D3.2c+torsion bound
- `nat_le_four_mul_totient_sq` — pure-Nat inequality, fully proved
- `totient_torsionOrder_le_finrank` — cyclotomic bridge, proved
- `torsionOrder_bound` — fully proved Lean code (combines the above two)
- `classNumber_eq_residue_formula` — analytic class number formula as algebraic identity, proved
- `card_ideals_of_norm_le_bound` — crude `2^((N!)^[K:ℚ])` bound, proved
- D3.1 decomposition: `hmr_brd_cm_tower` split into `gs_cm_tower` + `chebotarev_fixed_Q` with proved assembly

### How the 4 sorries break down

**Sorries 1 & 2 (proof path)**: blocked on substantial Mathlib gaps in algebraic number theory.
- *Sorry 1* needs Artin reciprocity (class field theory) — currently NOT in Mathlib at all.  Mathlib's roadmap includes this but it's a multi-year effort.
- *Sorry 2* needs Chebotarev density — partially blocked on Mathlib's L-function infrastructure.

**Sorries 3 & 4 (off-path)**: blocked on Mathlib's L-function analytic continuation.
- Both depend on the functional equation for `dedekindZeta` (Hecke gamma factors).
- *Sorry 3* (Friedman) additionally needs Mellin transforms of theta-like series.
- *Sorry 4* (Louboutin) additionally needs Phragmén–Lindelöf interpolation.

### What's NOT a blocker

The geometric, combinatorial, and CM-field class-group infrastructure is fully proved:
- Theorem 2.3 (planar set from datum)
- Lemma 2.4 (coset averaging)
- Proposition 2.2 / 3.2–3.6 (CM lift + lattice + class-group pigeonhole)
- All Q²-scaling integrality (Phase A)
- Q²-scaled Minkowski lattice (Phase C)
- Cyclotomic split-prime data (Phase D1+D2)

The complete proof flow goes through these without sorries; the four remaining gaps are localized to the algebraic number theory layer.

## File structure overview

- `Erdos90/` — the main formalization
- `Erdos90/Mathlib4_Extra/` — Mathlib-PR-shaped lemmas, mostly proved
- `assets/` — papers, tex sources, research notes
- `assets/search_results/` — focused research summaries (D3.1, D3.2 docs)
- `assets/hmr_2021_src/` — HMR 2021 tex source (Hajir-Maire-Ramakrishna)
- `assets/akhtari_vaaler_widmer_src/` — AVW 2025 tex source

## Notes from the maintainer (kept in scope)

- `README.md` is strictly human-only — agent must never edit
- Never force-push; that's the human's job
- AI time estimates don't apply (an AI working 5 minutes ≥ a human's 6 hours)
- For non-optimal but sufficient statements, leave comments rather than over-optimizing
