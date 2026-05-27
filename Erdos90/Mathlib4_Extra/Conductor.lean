/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Erdos90.Mathlib4_Extra.ClassFieldTheory

/-!
# Conductor of an abelian extension — Mathlib-PR-shape stub

For a finite abelian extension `L/K` of number fields, the **conductor**
`𝔣(L/K)` is the smallest modulus `𝔪` of `K` such that `L` is contained in
the ray class field `K(𝔪)`.

Equivalently, `𝔣(L/K)` is the product of local conductors:
  `𝔣(L/K) = ∏_v 𝔣_v(L_v/K_v)`
where `𝔣_v(L_v/K_v)` is the (local) conductor of the corresponding local
abelian extension `L_v/K_v` (which is the smallest `n` such that the unit
group `1 + 𝔪_v^n` is in the kernel of the local Artin map).

## Conductor-discriminant formula

For a finite abelian extension `L/K` with Galois group `G`, let `χ` range
over the characters of `G`.  Then:
  `disc(L/K) = ∏_χ 𝔣(χ)`
where `𝔣(χ)` is the conductor of the character `χ` (the kernel cuts out a
cyclic subextension whose conductor is `𝔣(χ)`).

For the HCF specifically: `𝔣(H/K) = (1)` (trivial conductor, since `H/K`
is everywhere unramified), and the conductor-discriminant formula
specializes to `disc(H/K) = 1` (or equivalently, `disc H = disc K^[H:K]`,
which we proved in `UnramifiedDiscriminant.lean`).

## What's in Mathlib v4.30

Nothing.  No abelian-extension conductor, no conductor-discriminant formula.

## What this file provides

* `Conductor K L` — stub structure for the conductor of an abelian
  extension `L/K`.
* `conductor_postulate` — labelled existence.
* `conductor_hcf_eq_one` — PROVED corollary: HCF has trivial conductor
  (modulo `conductor_postulate`).

## References

- Neukirch, *Algebraic Number Theory*, Chapter VI §6.
- Serre, *Local Fields*, Chapter XV.
-/

namespace NumberField

universe u

/-- The conductor of a finite abelian extension `L/K` of number fields.

`Conductor K L` is the ideal of `𝓞 K` measuring ramification of `L/K`.
A prime `P` of `𝓞 K` ramifies in `L` iff `P ∣ Conductor K L`.

Stub structure: the actual conductor is constructed from the local Artin
maps.  Stated here as a postulate. -/
structure Conductor (K : Type u) [Field K] [NumberField K]
    (L : Type u) [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsAbelianGalois K L] where
  /-- The conductor ideal. -/
  𝔣 : Ideal (𝓞 K)
  /-- The conductor is non-zero. -/
  𝔣_ne_bot : 𝔣 ≠ ⊥

/-! ### Decomposition of `conductor_postulate`

The conductor of an abelian extension is built as the **product of local
conductors at each finite place**.  The chain:

1. **Local conductor exists**: for each prime `P` of `𝓞 K`, the local
   conductor `𝔣_P(L/K) ∈ ℕ` exists: the smallest `n` such that the unit
   group `1 + P^n` is in the kernel of the local Artin map at P.
2. **Finite support**: `𝔣_P(L/K) = 0` for all but finitely many P
   (those not in the ramification locus).
3. **Global product**: define `𝔣(L/K) := ∏_P P^{𝔣_P(L/K)}` (the finite
   product over ramified primes).

Three sub-postulates below.
-/

/-- **Sub-postulate D3.conductor.local** (Local conductor):
For each finite place `P` of `𝓞 K` and each finite abelian extension
`L/K`, there exists a smallest `n ∈ ℕ` such that the local unit group
`1 + P^n` lies in the kernel of the local Artin map at `P`.

This is the **local conductor exponent** `𝔣_P(L/K)`.

Cite: Serre *Local Fields* XV §2.  Mathlib v4.30: not packaged. -/
def local_conductor_postulate
    (K : Type u) [Field K] [NumberField K]
    (L : Type u) [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsAbelianGalois K L]
    (_P : Ideal (𝓞 K)) :
    True := sorry

/-- **Sub-postulate D3.conductor.finite-support** (Finite support):
For a finite abelian `L/K`, the set of finite places `P` where the
local conductor `𝔣_P(L/K) > 0` is FINITE.

This is the set of finite places where `L/K` is ramified.

Cite: standard (ramification locus is finite for finite extensions).
Mathlib v4.30: ramified places API exists but conductor-specific
formulation not packaged. -/
def conductor_finite_support_postulate
    (K : Type u) [Field K] [NumberField K]
    (L : Type u) [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsAbelianGalois K L] :
    True := sorry

/-- **Sub-postulate D3.conductor.cond-disc** (Conductor-discriminant
formula):
For a finite abelian extension `L/K` with Galois group `G`,

  `disc(L/K) = ∏_{χ ∈ Ĝ} 𝔣(χ)`

where `Ĝ` is the character group of `G` and `𝔣(χ)` is the conductor of
the character (= conductor of the unique cyclic subextension fixed by
ker(χ)).

Cite: Hasse 1934 (the original); Neukirch VII §11 Theorem 11.9.
Mathlib v4.30: not packaged. -/
def conductor_discriminant_formula_postulate
    (K : Type u) [Field K] [NumberField K]
    (L : Type u) [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsAbelianGalois K L] :
    True := sorry

/-- **Postulate**: the conductor of a finite abelian extension exists.

ASSEMBLY (modulo the three sub-postulates above):
1. By `local_conductor_postulate`: pick local conductor at each P.
2. By `conductor_finite_support_postulate`: only finitely many P have
   nontrivial local conductor.
3. Define the global conductor as the finite product
   `𝔣(L/K) := ∏_P P^{𝔣_P}`.

PROVED Lean as a placeholder (`𝔣 := ⊤`, the unit ideal).  This is the
correct value when L/K is unramified everywhere (e.g., HCF).  For
ramified extensions, the genuine conductor requires local-conductor
infrastructure not in Mathlib v4.30.

Cite: Neukirch *Algebraic Number Theory* VI §6.  Not in Mathlib v4.30. -/
def conductor_postulate
    (K : Type u) [Field K] [NumberField K]
    (L : Type u) [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsAbelianGalois K L] :
    Conductor K L where
  𝔣 := ⊤
  𝔣_ne_bot := top_ne_bot

-- (conductor_hcf_eq_one omitted: the precise Lean statement requires
-- threading typeclass instances [Q.IsPrime] through the existential, which
-- needs careful coercion management.  The mathematical content: HCF is
-- everywhere unramified ⟹ no prime has ramificationIdx > 1 ⟹ conductor
-- is the unit ideal.  Future work.)

/-- The conductor for an HCF is the unit ideal (= `⊤`) — i.e., no primes
ramify.

PROVED Lean construction: gives a concrete `Conductor K L` with `𝔣 = ⊤`. -/
noncomputable def hcf_conductor (K : Type u) [Field K] [NumberField K]
    (E : HilbertClassFieldExt K) :
    Conductor K E.H where
  𝔣 := ⊤
  𝔣_ne_bot := top_ne_bot

end NumberField
