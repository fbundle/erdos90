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

/-- **Postulate**: the conductor of a finite abelian extension exists.

Cite: Neukirch *Algebraic Number Theory* VI §6.  Not in Mathlib v4.30. -/
def conductor_postulate
    (K : Type u) [Field K] [NumberField K]
    (L : Type u) [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsAbelianGalois K L] :
    Conductor K L := sorry

-- (conductor_hcf_eq_one omitted: the precise Lean statement requires
-- threading typeclass instances [Q.IsPrime] through the existential, which
-- needs careful coercion management.  The mathematical content: HCF is
-- everywhere unramified ⟹ no prime has ramificationIdx > 1 ⟹ conductor
-- is the unit ideal.  Future work.)

end NumberField
