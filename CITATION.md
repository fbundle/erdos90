# Citation

This project builds on prior Lean 4 / Mathlib formalization work.  Whenever we
use, port, or adapt external code, we cite the source here.

## Primary external Lean dependencies

### `vendor/mathlib4/`

The **Lean Mathematical Library** (Mathlib4), version v4.30.0.

* Project: https://github.com/leanprover-community/mathlib4
* License: Apache 2.0
* Citation: The mathlib Community. "The Lean mathematical library." CPP 2020.
* Used as: primary Lean dependency (via `[[require]]` in `lakefile.toml`).

### `vendor/formal-conjectures/`

The **Google DeepMind Formal Conjectures** project.

* Project: https://github.com/google-deepmind/formal-conjectures
* Used as: reference for the Lean template of Erdős Problem 90 (see
  `FormalConjectures/ErdosProblems/90.lean`).

### `vendor/ClassFieldTheory/` (Kevin Buzzard's CFT project)

The **2025 Clay Maths Summer School on Formalizing Class Field Theory** repo,
maintained by Kevin Buzzard.

* Original project: https://github.com/kbuzzard/ClassFieldTheory
* Local fork (with v4.30 bump): https://github.com/fbundle/ClassFieldTheory
* License: Apache 2.0
* Contributors (per file headers): Kevin Buzzard, Yaël Dillies, Aaron Liu,
  María Inés de Frutos-Fernández, and the 2025 Clay summer school participants.

**What we use from it (intended targets, work-in-progress):**

* `Cohomology/LocalInv.lean` — local invariant `H²(ℤ/nℤ, ℤ) ≃+ ZMod n`.
  Underlying the abstract reciprocity isomorphism.
* `Cohomology/TateCohomology.lean` — Tate cohomology framework.
* `Cohomology/SplittingModule.lean` — `FiniteClassFormation` + abstract
  Artin `reciprocityIso`.
* `IsNonarchimedeanLocalField/HerbrandQuotient.lean` — Herbrand quotient.
* `IsNonarchimedeanLocalField/Basic.lean` and friends — non-archimedean local
  field foundations (valuations, ramification, towers).

**Status (as of 2026-05-27):** the upstream Buzzard repo uses Lean v4.29.0 and
Mathlib v4.29; we use v4.30.  We bumped a local fork of his repo to v4.30 and
fixed about half of the v4.30 API drift errors (in `Mathlib/RingTheory/Unramified/LocalRing.lean`,
`Cohomology/IndCoind/Finite.lean`, `Cohomology/{Tate,SerreApproximation}.lean`,
`Mathlib/RepresentationTheory/.../Basic.lean`, `IsNonarchimedeanLocalField/Basic.lean`).
The remaining errors are mostly `simp` set drift in `TateCohomology.lean` and
`SerreApproximation.lean`, plus one missing instance (`IsBotZeroClass (ValueGroup₀ vK)`).

When we successfully port a Buzzard lemma into our codebase (e.g. into
`Erdos90/Mathlib4_Extra/Vendor/CFT/`), the file header MUST include:

```
/-
Copyright (c) <year> <original authors>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <original authors> (from kbuzzard/ClassFieldTheory)
Adapted for Erd46 by: Khanh Nguyen with Claude Opus 4.7

Source: https://github.com/kbuzzard/ClassFieldTheory
       commit <sha>
-/
```

## Other referenced (but not yet ported) external work

These are referenced in our `Erdos90/Mathlib4_Extra/*.lean` postulate docstrings
as the eventual Mathlib home for the relevant theorem.  We have NOT copied any
code from them yet.

### `mariainesdff/local_fields_journal`

María Inés de Frutos-Fernández's **Local Fields** formalization (CPP 2024).

* Project: https://github.com/mariainesdff/local_fields_journal
* Referenced in: `Erdos90/Mathlib4_Extra/LocalCFT.lean` (as the upstream-candidate
  for the local CFT chain).

### Loeffler–Stoll "Formalizing zeta and L-functions in Lean" (arXiv:2503.00959)

* Paper: https://arxiv.org/abs/2503.00959
* Status: results being contributed to Mathlib; covers Riemann zeta + Dirichlet
  L-functions and the formal statement of the Riemann hypothesis.
* Referenced in: `Erdos90/Mathlib4_Extra/DedekindZetaFE.lean` and
  `Erdos90/Mathlib4_Extra/HeckeCharacters.lean` (these are the analytic-chain
  postulates that Loeffler-Stoll's work would eventually support for `ζ_K`).

## Reference papers and texts (for postulate citations)

Many of our `Erdos90/Mathlib4_Extra/*.lean` postulates cite primary mathematical
sources rather than other Lean formalizations.  These are the "external math"
the formalization rests on, not Lean code dependencies:

* OpenAI 2026 — *Planar Point Sets with Many Unit Distances*
  (`assets/unit-distance-proof.pdf`): the paper proving Theorem 1.1.
* Hajir-Maire-Ramakrishna 2021 — *Cutting Towers* (`assets/hmr_2021_src/`): the
  Golod-Shafarevich CM tower with bounded root discriminant.
* Friedman 1989 *Analytic formulas for the regulator of a number field*
  (Inventiones 98:599-622).
* Louboutin 2000 *Explicit upper bounds for residues of Dedekind zeta functions
  and class numbers of CM-fields* (`assets/louboutin_2000_class_number.pdf`).
* Hecke 1917, Tate's thesis 1950 (dedekindZeta functional equation).
* Lubin-Tate 1965 (local Artin map via formal groups).
* Stickelberger 1890 (Stickelberger element + annihilation).
* Mazur-Wiles 1984, Wiles 1990 (Iwasawa Main Conjecture).
* Brauer 1947 (induction theorem for L-functions).
* Hasse 1933, Brauer-Hasse-Noether 1932 (Hasse principle for algebras).
* Iyanaga 1934, Tannaka 1934 (Verlagerung vanishing / group-theoretic principal
  ideal theorem).

## License compatibility

All cited Lean projects are under Apache 2.0, which is compatible with this
project's Apache 2.0 license.  Per Apache 2.0, derivative files retain
attribution to the original authors.
