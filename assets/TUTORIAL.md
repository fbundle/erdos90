# Tutorial: navigating the Erd46 formalization

A friendly walkthrough for newcomers to this codebase.

## What is this project?

A Lean 4 formalization of Theorem 1.1 from the OpenAI paper *"Planar Point
Sets with Many Unit Distances"* (2026), which disproves the Erdős
unit-distance conjecture:

> ∃ δ > 0 such that ν(n) ≥ n^{1+δ} for infinitely many n.

Here ν(n) = maximum number of unit-distance pairs among n points in the plane.

## Quick start

1. **Build:** `lake build` (requires `leanprover/lean4:v4.30.0-rc2`).
2. **Find the main theorem:** `Erdos90/Main.lean`, `erdos_unit_distance_false`.
3. **Check axioms:**
   ```
   info: Erdos90/Main.lean:221:0: 'erdos_unit_distance_false' depends on axioms:
     [propext, sorryAx, Classical.choice, Quot.sound]
   ```
   The `sorryAx` indicates 4 documented sorries (see below).

## File map

| Section | Files | Status |
|---|---|---|
| Geometric construction | `Geometric.lean`, `DiscGeometry.lean`, `Defs.lean` | Fully proved |
| Coset averaging | `CosetAveraging.lean` | Fully proved |
| Number field engine | `NumberField.lean`, `Arithmetic.lean` | Proved modulo NumberFieldDeep sorries |
| Deep NT | `NumberFieldDeep_*.lean` (5 files) | Proved modulo 2 HMR sorries |
| CM field machinery | `CMField/*.lean` (5 files) | Fully proved |
| Mathlib extensions | `Mathlib4_Extra/*.lean` | Proved modulo 2 analytic sorries |
| Main theorem | `Main.lean` | Fully proved (via everything else) |

## The 4 remaining sorries

All are blocked on Mathlib infrastructure that doesn't yet exist.

### Proof-path sorries

1. **`gs_cm_tower`** (in `NumberFieldDeep_GSTower.lean`) —
   Golod–Shafarevich existence of a CM tower with bounded root discriminant.
   Blocked on Mathlib class field theory.

2. **`chebotarev_fixed_Q`** (in `NumberFieldDeep_GSTower.lean`) —
   Chebotarev/Ihara fixed split primes across the tower.
   Blocked on Mathlib Chebotarev density.

### Off-path infrastructure sorries

3. **`regulator_lower_bound_cm`** (in `Mathlib4_Extra/ClassNumberBound.lean`) —
   Friedman 1989 bound `R_K ≥ 0.2052`.

4. **`dedekind_residue_upper_bound_cm`** (in `Mathlib4_Extra/ClassNumberBound.lean`) —
   Louboutin 2000 residue upper bound.

Sorries 3 and 4 share the same Mathlib gap (functional equation of `dedekindZeta`).

## Reading order

### 5-minute summary
1. `README.md` — project description (human-maintained)
2. `REPORT.md` — current status (high level)
3. `assets/proof_outline.md` — 10-step proof walkthrough

### 1-hour deep dive
1. `assets/proof_outline.md` — start here
2. `Erdos90/Main.lean` — the main theorem statement
3. `Erdos90/Geometric.lean` — the geometric construction (Theorem 2.3)
4. `Erdos90/NumberField.lean` — parameter setup (`exists_admissible_family`)
5. `Erdos90/NumberFieldDeep_GSTower.lean` — the tower/chain assembly + sorries
6. `Erdos90/Mathlib4_Extra/ClassNumberBound.lean` — the chain decomposition

### Contributing to closing sorries
1. `assets/search_results/closing_roadmap.md` — 5-PR Mathlib strategy
2. `assets/search_results/mathlib_lseries_infrastructure.md` — Mathlib gap analysis
3. `assets/search_results/loeffler_stoll_lfunctions_in_lean.md` — Loeffler-Stoll template
4. `assets/mathlib_pr_candidates.md` — list of extractable Mathlib PRs
5. `assets/mathlib_pr_drafts/` — actual Lean files ready to submit

## Maintaining the project

### Build / commit conventions
- `lake build` should always succeed.
- The 4 sorry warnings + axiom info line are the expected output.
- Commit messages should reference the phase (D5, E13, etc.) when relevant.

### Adding a new sorry (don't)
- Avoid adding new sorries.  If you must, document the reason precisely.
- Prefer decomposing existing sorries into smaller named pieces (see how
  D5 and E10 split larger sorries into Mathlib-PR-shaped sub-pieces).

### Closing a sorry
1. Verify the closure builds: `lake build`.
2. Confirm `erdos_unit_distance_false` depends only on standard axioms:
   ```
   #print axioms erdos_unit_distance_false
   ```
3. Update relevant docstrings + `CLAUDE.md` + `REPORT.md`.
4. Commit with a phase number (e.g. "Phase E13").

## Key strategic insights

1. **Sorries 3 and 4 share infrastructure.** Both need the functional
   equation for `dedekindZeta`.  Build that ONE piece of Mathlib and BOTH
   close.

2. **The Loeffler-Stoll 2025 paper is the template.** They formalized
   Riemann zeta + Dirichlet L-functions in Mathlib using the
   theta-function-via-Poisson-summation architecture.  The same architecture
   generalizes to Dedekind zeta for general K.

3. **Class field theory (for sorry 1) is a separate Mathlib roadmap.** Not
   shared with the off-path sorries.  Multi-year effort.

4. **The geometric/combinatorial layer is fully closed.** Theorem 2.3,
   Lemma 2.4, the disc-overlap analysis are all proved.  The remaining
   gaps are purely algebraic NT.

## Where to look for specific things

| What you want | Where |
|---|---|
| Main theorem statement | `Erdos90/Main.lean` |
| Parameter constants (δ, R, etc.) | `Erdos90/Arithmetic.lean`, `Defs.lean` |
| The 4 sorries | search for ` := sorry$` in `Erdos90/` |
| Mathlib PR drafts | `assets/mathlib_pr_drafts/` |
| Research notes | `assets/search_results/` |
| Source papers | `assets/*.pdf`, `assets/*_src/` |
| Build instructions | `README.md` |

## Conventions

- **CLAUDE.md** — agent-targeted (the AI working on the project)
- **README.md** — human-only (never edit programmatically)
- **REPORT.md** — human-readable progress log
- **TUTORIAL.md** — this file (newcomer-facing)
- **SESSION_NOTE_*.md** — overnight session retrospectives
- **assets/proof_outline.md** — end-to-end walkthrough
- **assets/mathlib_pr_candidates.md** — extractable contributions
- **assets/search_results/** — research notes (organized per sorry)

## Getting help

- The codebase is well-commented; start with the file/lemma docstrings.
- See `CLAUDE.md` for substantial agent-targeted documentation (also useful
  for humans).
- The `assets/search_results/INDEX.md` is the entry point to all research
  material.
