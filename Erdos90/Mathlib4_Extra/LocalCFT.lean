/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Erdos90.Mathlib4_Extra.ClassFieldTheory

/-!
# Local class field theory — Mathlib-PR-shape stub

For a local field `K_v` (the completion of a number field `K` at a place `v`),
local class field theory provides the **local Artin map**:

  `K_v^* → Gal(K_v^{ab}/K_v)`

which is an isomorphism `K_v^* / N_{L/K_v}(L^*) ≅ Gal(L/K_v)` for any finite
abelian extension `L/K_v`.

This is the building block for global class field theory (the global Artin
map is constructed by patching together local ones at each place).

## What's in Mathlib v4.30

A partial local CFT exists as an EXTERNAL project at
<https://github.com/mariainesdff/LocalClassFieldTheory> (Maria Inés de
Frutos-Fernández).  Not yet in Mathlib core.

## What this file provides

Labelled postulates for:
* `LocalField` predicate (already in `Mathlib/NumberTheory/LocalField`).
* `localArtinMap` — the local Artin map (postulated).
* `localNormGroup` — the norm group of a finite abelian extension.
* `localConductor` — the conductor of a finite abelian character.

## References

- Serre, *Local Fields*, Chapter XI.
- Neukirch, *Algebraic Number Theory*, Chapter V.
- Frutos-Fernández's `LocalClassFieldTheory` GitHub repo.
-/

namespace NumberField

universe u

/-! ## The local Artin map

For a finite abelian extension `L/K_v` of a local field, the local Artin map
is a surjective homomorphism `K_v^* → Gal(L/K_v)` with kernel `N_{L/K_v}(L^*)`.
-/

/-- **Postulate**: the local Artin map for a finite abelian extension of a
local field.

The map `K_v^* → Gal(L/K_v)` sends `x` to the Frobenius element of the
prime ideal `(x) ⊆ 𝓞_{K_v}` (suitably defined for non-units).

Cite: Serre *Local Fields* XI §3.  Not in Mathlib v4.30 (see Frutos-Fernández's
`LocalClassFieldTheory` for partial formalization). -/
def localArtinMap_postulate
    (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
    [IsGalois K L] [IsAbelianGalois K L] :
    Kˣ →* (L ≃ₐ[K] L) := sorry

/-- **Postulate** (universal property of the local Artin map):

The local Artin map is surjective, with kernel exactly the image of the
norm map `L^* → K^*`. -/
def localArtinMap_surjective_postulate
    (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
    [IsGalois K L] [IsAbelianGalois K L] :
    Function.Surjective (localArtinMap_postulate K L) := sorry

/-! ## Norm group and conductor

For a finite abelian extension `L/K_v` of local fields, the norm group
`N_{L/K_v}(L^*) ⊆ K_v^*` is a subgroup of finite index `[L : K_v]`.

The conductor `𝔣(L/K_v)` is the smallest `n` such that the unit group
`1 + 𝔪^n ⊆ N_{L/K_v}(L^*)` (where `𝔪` is the maximal ideal of `𝓞_{K_v}`).
-/

/-- The norm group of a finite abelian extension of local fields. -/
def localNormGroup_postulate
    (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
    [IsGalois K L] [IsAbelianGalois K L] :
    Subgroup Kˣ := sorry

end NumberField
