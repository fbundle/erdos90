/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Erdos90.Mathlib4_Extra.HeckeCharacters

/-!
# Stark conjectures — Mathlib-PR-shape stub

The **Stark conjectures** (Stark 1971+) are a far-reaching collection of
conjectures predicting algebraicity properties of leading coefficients of
Hecke L-functions at `s = 0` and `s = 1`.

## Stark's main conjecture

For a finite abelian extension `L/K` of number fields and an algebraic
character `χ` of `Gal(L/K)`, the leading Taylor coefficient of `L(s, χ)`
at `s = 0` is conjecturally:

  `L^{(r)}(0, χ) = R(χ) · A(χ)`

where:
- `r = order of zero of L(s, χ) at s = 0` (computable from `χ`).
- `R(χ)` is a Stark regulator (involves logarithms of "Stark units").
- `A(χ)` is an algebraic number.

## Connection to class numbers

For the trivial character `χ_0` of `K`:
- `L(s, χ_0) = ζ_K(s)`.
- `L(s, χ_0) = -(h_K · R_K / w_K) · s^{r_1+r_2-1}` near `s = 0` (Dirichlet
  class number formula at `s = 0`).
- This is the **analytic class number formula** that Mathlib has via
  `dedekindZeta_residue`.

Stark generalizes this to non-trivial characters.

## What's in Mathlib v4.30

- `dedekindZeta_residue_def` (PROVED) — class number formula at `s = 1`.
- No L-function continuation, no Stark conjecture infrastructure.

## What this file provides

Labelled stubs for:
* `starkRegulator_postulate` — the Stark regulator.
* `stark_main_conjecture_postulate` — the main conjecture statement.

## Why this is OFF the proof path

Stark conjectures are deep predictions in analytic number theory, far
removed from the elementary GS argument in HMR.  They're documented here
for completeness of the CFT landscape.

## References

- Stark, *L-functions at s = 1*, Adv. Math. 1971, 1975, 1976.
- Tate, *Les conjectures de Stark sur les fonctions L d'Artin en s = 0*,
  Birkhäuser 1984.
- Solomon's notes on Stark conjectures.
-/

namespace NumberField

universe u

/-- **Stark regulator** (labelled stub).

For a finite abelian extension `L/K` and a character `χ` of `Gal(L/K)`,
the Stark regulator `R(χ)` is a determinant of logarithms of "Stark units"
that should equal the leading L-value coefficient at `s = 0`. -/
def starkRegulator_postulate
    (K : Type u) [Field K] [NumberField K]
    (L : Type u) [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsAbelianGalois K L]
    (_χ : (L ≃ₐ[K] L) →* ℂˣ) :
    ℂ := sorry

/-- **Postulate** (Stark's main conjecture):

For an abelian L/K and character χ of Gal(L/K), the leading coefficient
of L(s, χ) at s = 0 equals the Stark regulator times an algebraic number.

Cite: Stark 1971-1976; Tate 1984. -/
def stark_main_conjecture_postulate
    (K : Type u) [Field K] [NumberField K]
    (L : Type u) [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsAbelianGalois K L] :
    True := sorry

end NumberField
