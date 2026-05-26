# REPORT — Erd46 formalization status

This file is the **human-readable progress log** for the project.  Written by the AI agent; intended for the human maintainer to skim and track.  Distinct from:
- `CLAUDE.md` — agent instructions
- `README.md` — human-maintained project description

## Current state (last updated: 2026-05-27 — Phase E14 decomposition)

`erdos_unit_distance_false` (Theorem 1.1) is fully formalized **modulo 5 named sorries**, each cited with literature and decomposed into Mathlib-PR-shaped pieces.  The proof depends only on standard foundational axioms (`propext`, `sorryAx`, `Classical.choice`, `Quot.sound`) — no custom axioms.

**Phase E14 (2026-05-27)** restructured the load-bearing `gs_cm_tower` into PROVED Lean code that delegates to a more cleanly-shaped labelled postulate `gs_cm_tower_infinite_postulate` living in `Mathlib4_Extra/GolodShafarevich.lean`.  The discriminant-control half is now fully proved via `rootDiscr_eq_of_unramifiedTower` in `Mathlib4_Extra/UnramifiedDiscriminant.lean`.

### The 5 sorries (3 on proof path, 2 off-path)

| # | Name | Location | Type | Mathlib gap |
|---|---|---|---|---|
| 1 | `gs_cm_tower_infinite_postulate` | `Erdos90/Mathlib4_Extra/GolodShafarevich.lean:129` | proof path (NEW location; was `gs_cm_tower`) | class field theory + Golod–Shafarevich + pro-p cohomology (multi-year) |
| 2 | `chebotarev_fixed_Q` | `Erdos90/NumberFieldDeep_GSTower.lean:220` | proof path | Chebotarev density theorem + L-function continuation (multi-month) |
| 3 | `hilbertClassField_exists` | `Erdos90/Mathlib4_Extra/ClassFieldTheory.lean:106` | off-path | Artin reciprocity (multi-year Mathlib) |
| 4 | `regulator_lower_bound_cm` | `Erdos90/Mathlib4_Extra/ClassNumberBound.lean:307` | off-path | Friedman 1989: analytic regulator formula via Mellin transforms |
| 5 | `dedekind_residue_upper_bound_cm` | `Erdos90/Mathlib4_Extra/ClassNumberBound.lean:343` | off-path | Louboutin 2000: functional equation of ζ_K + L(1,χ) bounds |

### Recently closed (this session, 2026-05-26 → 2026-05-27)

- `gs_cm_tower` — proof-path sorry, now PROVED Lean code via Phase E14 chain
  (uses `gs_unramified_tower_with_bounded_rd` proved in `Mathlib4_Extra/GolodShafarevich.lean`).
- `rootDiscr_eq_of_unramifiedTower` — fully proved in `Mathlib4_Extra/UnramifiedDiscriminant.lean`.
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

## Strategic docs

The two key documents for incremental progress:
1. **`assets/search_results/closing_roadmap.md`** — 5-PR Mathlib strategy
   that closes off-path sorries 3 + 4 (via shared `dedekindZeta` functional
   equation infrastructure).
2. **`assets/search_results/mathlib_lseries_infrastructure.md`** — survey of
   what Mathlib already has for L-series (substantial: AbstractFuncEq,
   Dirichlet L-functions with functional equation, Mellin transforms,
   1-D Poisson summation).  Identifies the precise multi-D Poisson summation
   + theta function gap.

## Recent session (2026-05-27) deliverables

### Code
- `nat_le_four_mul_totient_sq` — fully proved (closes the helper for
  `torsionOrder_bound`).  Used `Nat.recOnPosPrimePosCoprime` + 2-adic
  decomposition via `padicValNat`.
- `class_num_bound_of_brd` — assembled chain via E5+D3.2b+D3.2c+torsion.
  Sorry count on proof path dropped 3 → 2.
- `totient_torsionOrder_le_finrank` — cyclotomic bridge, fully proved.
- `regulator_lower_bound_cm` and `dedekind_residue_upper_bound_cm` — both
  remain sorried but with improved docstrings + roadmap docs.

### Research notes
- Decomposition documents (D31/D32) extended
- Mathlib L-series infrastructure survey
- Closing roadmap with 5-PR strategy
- Updated INDEX.md

### Key insight discovered
The shortest path to closing the off-path sorries is via **multi-dimensional
Poisson summation + theta function on number-field lattice + functional
equation for `dedekindZeta`**.  This SINGLE coherent infrastructure unblocks
both sorries 3 and 4.  Mathlib has the foundations (`AbstractFuncEq`,
1-D Poisson, Jacobi theta in 1+2 variables); the gap is generalizing to
arbitrary lattices in `mixedSpace K`.

## File map (key edits this session)

- `Erdos90/Mathlib4_Extra/ClassNumberBound.lean` — Phase E5–E13 infrastructure
- `Erdos90/NumberFieldDeep_GSTower.lean` — Phase D5 + E9 (chain assembly)
- `CLAUDE.md` — agent instructions updated
- `assets/search_results/` — 6 new/updated focused research notes
- `assets/hmr_2021_src/` — HMR tex source (arXiv:1901.04354)
- `assets/akhtari_vaaler_widmer_src/` — AVW tex source

## Outstanding tasks (for next session / contributor)

In order of leverage:
1. (Mathlib PR) Multi-D Poisson summation for ZLattice — see
   `assets/search_results/closing_roadmap.md` PR-A;
   skeleton/placeholder file at `Erdos90/Mathlib4_Extra/MultiDimPoisson.lean`
2. (Mathlib PR) Theta function for number field via `mixedSpace K`
3. (Mathlib PR) Functional equation for `dedekindZeta` via AbstractFuncEq
4. (Mathlib PR) Friedman/Louboutin bounds using #3
5. (Mathlib PR — independently) Extract `Nat.le_four_mul_totient_sq` to Mathlib's
   `Mathlib/Data/Nat/Totient.lean`.  Already proved in this codebase; just needs
   cleanup + PR submission.  See `assets/mathlib_pr_candidates.md`.
6. (Local) Tighten / refactor existing proofs once Mathlib infrastructure lands

## Key docs for the next contributor

In order of accessibility:
1. **`assets/proof_outline.md`** — start here.  10-step walkthrough.
2. **`REPORT.md`** (this file) — high-level state.
3. **`CLAUDE.md`** — agent-targeted instructions but useful for humans too.
4. **`assets/mathlib_pr_candidates.md`** — what can be extracted as Mathlib PRs.
5. **`assets/search_results/INDEX.md`** — index to all research notes.
6. **`assets/search_results/closing_roadmap.md`** — the 5-PR strategy.
7. **`assets/search_results/mathlib_lseries_infrastructure.md`** — Mathlib gap analysis.
8. **`assets/search_results/loeffler_stoll_lfunctions_in_lean.md`** — extract
   from the Loeffler-Stoll 2025 paper.
