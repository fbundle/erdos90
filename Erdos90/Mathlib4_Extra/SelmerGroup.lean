/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Erdos90.Mathlib4_Extra.GaloisCohomology

/-!
# Selmer groups — Mathlib-PR-shape stub

The **Selmer group** of an algebraic group / Galois module is a refinement
of the first Galois cohomology that's bounded by local conditions.

For an elliptic curve `E/K`, the n-Selmer group `Sel_n(E/K) ⊆ H¹(K, E[n])`
is defined by local conditions at every place.

For the **classical CFT** setting:
- Class field theory gives `H²(K, ℤ_p(1)) ≅ Sel_p(Gm/K) = `p`-Selmer of Gm`.
- This generalizes to higher-dimensional algebraic groups.

## Connection to Iwasawa Main Conjecture

The Iwasawa Main Conjecture (Mazur–Wiles 1984 for `ℚ`, Wiles 1990 for
totally real fields) is a STATEMENT about Selmer groups:

  `char(Sel_p(K_∞)) = char(p-adic L-function)`

where `char` is the characteristic ideal of a Λ-module, and `K_∞/K` is
a Zp-extension.

For HMR / Erd46, this is **far off the proof path**.  But it's the
ultimate destination of the Iwasawa-theoretic framework underlying HMR.

## What's in Mathlib v4.30

- Group cohomology infrastructure (referenced in `GaloisCohomology.lean`).
- No Selmer groups, no Iwasawa Main Conjecture.

## What this file provides

Labelled stubs documenting the Selmer-group landscape.

## References

- Mazur–Wiles, *Class fields of abelian extensions of Q*, Invent. Math. (1984).
- Wiles, *The Iwasawa conjecture for totally real fields*, Ann. of Math. (1990).
- Kato, *p-adic Hodge theory and values of zeta functions of modular forms*,
  Astérisque (2004).
- Greenberg, *Iwasawa theory, projective modules, and modular representations*,
  Memoirs AMS (2010).
-/

namespace NumberField

universe u

/-- **Selmer group** for an algebraic group (labelled stub).

For a Galois module M and integer n, the n-Selmer group is the subgroup
of `H¹(K, M)` defined by local conditions (Selmer's class-field-theoretic
trivialization at every place).

This stub captures the structural existence; the precise definition depends
on the choice of local conditions. -/
def SelmerGroup_postulate
    (K : Type u) [Field K] [NumberField K] (_n : ℕ) :
    Type := Unit  -- placeholder

/-- **Iwasawa Main Conjecture** (labelled, far off-path):

For a totally real number field K and a prime p, the characteristic ideal
of the Iwasawa module `X_∞ = Gal(M_∞/K_∞)` (where M_∞ is the maximal
unramified abelian p-extension of the cyclotomic Zp-extension `K_∞`) equals
the characteristic ideal of the p-adic L-function.

Cite: Mazur–Wiles 1984 (K = ℚ), Wiles 1990 (totally real K).  Not in
Mathlib v4.30. -/
def iwasawa_main_conjecture_postulate
    (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (p : ℕ) (_hp : Nat.Prime p) :
    True := sorry

end NumberField
