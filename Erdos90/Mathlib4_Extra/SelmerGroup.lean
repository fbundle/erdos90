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

/-! ### Decomposition of `iwasawa_main_conjecture_postulate`

Mazur-Wiles 1984's proof for ℚ (extended by Wiles 1990 to totally real K)
decomposes via the **Euler system of cyclotomic units / elliptic units**:

1. **Construction of Euler system**: build a system of compatible units
   `c_n ∈ K_n^*` over the cyclotomic tower satisfying norm relations.
2. **Kolyvagin derivative**: use the Euler system to construct derivative
   classes in Galois cohomology that bound the Iwasawa module's
   characteristic ideal from above.
3. **Lower bound from L-functions**: the Iwasawa Main Conjecture follows
   from showing the p-adic L-function generates an ideal that's also
   contained in the characteristic ideal (the lower bound).

Three sub-postulates below.
-/

/-- **Sub-postulate D3.imc.euler-system** (Euler system existence):
For each totally real number field K and prime p, there exists an
**Euler system** of cyclotomic units (or elliptic units for imaginary
quadratic K) compatible with the Iwasawa tower structure.

Cite: Kolyvagin 1990; Rubin *Euler Systems*.  Mathlib v4.30: not packaged. -/
def imc_euler_system_postulate
    (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (p : ℕ) (_hp : Nat.Prime p) :
    True := sorry

/-- **Sub-postulate D3.imc.kolyvagin-derivative** (Kolyvagin derivative):
Given an Euler system, the **Kolyvagin derivative construction** produces
elements of `H¹(K, V_p)` that bound the Selmer group from above.

Cite: Kolyvagin 1990; Rubin Ch. 3.  Mathlib v4.30: not packaged. -/
def imc_kolyvagin_derivative_postulate
    (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (p : ℕ) (_hp : Nat.Prime p) :
    True := sorry

/-- **Sub-postulate D3.imc.l-function-bound** (L-function lower bound):
The p-adic L-function `L_p(s, χ)` (Kubota-Leopoldt) generates an ideal
in the Iwasawa algebra contained in the characteristic ideal of the
Iwasawa module `X_∞`.

This is the "easy" direction in the IMC.  Cite: Iwasawa 1969 for ℚ;
Wiles 1990 for totally real.  Mathlib v4.30: not packaged. -/
def imc_l_function_bound_postulate
    (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (p : ℕ) (_hp : Nat.Prime p) :
    True := sorry

/-- **Iwasawa Main Conjecture** (labelled, far off-path):

For a totally real number field K and a prime p, the characteristic ideal
of the Iwasawa module `X_∞ = Gal(M_∞/K_∞)` (where M_∞ is the maximal
unramified abelian p-extension of the cyclotomic Zp-extension `K_∞`) equals
the characteristic ideal of the p-adic L-function.

ASSEMBLY (modulo the three sub-postulates above):
1. By `imc_l_function_bound_postulate`: L_p ⊆ char(X_∞) (one direction).
2. By `imc_euler_system_postulate`: build Euler system.
3. By `imc_kolyvagin_derivative_postulate`: char(X_∞) ⊆ L_p (other direction).

Cite: Mazur–Wiles 1984 (K = ℚ), Wiles 1990 (totally real K).  Not in
Mathlib v4.30. -/
def iwasawa_main_conjecture_postulate
    (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (p : ℕ) (_hp : Nat.Prime p) :
    True := sorry

end NumberField
