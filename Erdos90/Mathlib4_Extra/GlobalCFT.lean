/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Erdos90.Mathlib4_Extra.LocalCFT

/-!
# Global class field theory — Mathlib-PR-shape stub

For a number field `K`, global class field theory provides the **global
Artin map**:

  `J_K → Gal(K^{ab}/K)`

where `J_K = (AdeleRing K)ˣ` is the **idele group**, and `K^{ab}` is the
maximal abelian extension of `K`.

The global Artin map factors through the **idele class group**
`C_K = J_K / Kˣ`, giving an isomorphism

  `C_K^0 ≅ Gal(K^{ab}/K)`

(where `C_K^0` is the connected component of the identity in `C_K`).

## Hilbert class field as a quotient

The Hilbert class field `H(K)` corresponds (via the Artin map) to the kernel
`J_K^0 · Kˣ` where `J_K^0` is the subgroup of "everywhere-integral" ideles.
The quotient is

  `J_K / (J_K^0 · Kˣ) ≅ ClassGroup (𝓞 K) ≅ Gal(H(K)/K)`.

This is the precise statement of Artin reciprocity for HCF.

## What's in Mathlib v4.30

- `NumberField.AdeleRing K` — the full adele ring (PROVED).
- `NumberField.InfiniteAdeleRing K` (PROVED).
- `IsDedekindDomain.FiniteAdeleRing R K` (PROVED).
- No idele group, no global Artin map.

## What this file provides

* `IdeleGroup K` — alias for `(AdeleRing (𝓞 K) K)ˣ`.
* `IdeleClassGroup K` — quotient by principal ideles.
* `globalArtinMap_postulate` — the global Artin map (postulated).
* Documented connection to `HilbertClassFieldExt`.

## References

- Tate, *Global Class Field Theory*, in Cassels-Fröhlich.
- Neukirch, *Algebraic Number Theory*, Chapter VI.
-/

namespace NumberField

universe u

/-! ## Idele group -/

/-- The idele group `J_K` of a number field `K`: the unit group of the adele
ring.  An idele is a sequence `(x_v)_v` with `x_v ∈ K_v^*` for each place
`v`, and `x_v ∈ 𝓞_{K_v}^*` for almost all `v`. -/
abbrev IdeleGroup (K : Type u) [Field K] [NumberField K] : Type u :=
  (AdeleRing (𝓞 K) K)ˣ

-- (IdeleClassGroup = J_K / K^* — quotient by the principal idele subgroup.
-- Defining this cleanly requires constructing the subgroup of principal
-- ideles within IdeleGroup K, which uses adele ring's `principalSubgroup`
-- from Mathlib.  Left as future infrastructure work.)

/-! ## The global Artin map -/

/-- **Postulate**: the global Artin map for a number field.

For any number field `K`, there is a continuous surjective homomorphism
`J_K → Gal(K^{ab}/K)` whose kernel is `K^*` (the principal ideles), and
restricting to any finite abelian `L/K` gives the Artin reciprocity
isomorphism `J_K / (K^* · N_{L/K}(J_L)) ≅ Gal(L/K)`.

In particular, for the Hilbert class field `H(K)`:
- The Artin map factors through `J_K → ClassGroup (𝓞 K) ≃ Gal(H(K)/K)`.
- This is the `artinReciprocity` field of `HilbertClassFieldExt K`.

Cite: Tate, *Global Class Field Theory*, in Cassels-Fröhlich; Neukirch,
*Algebraic Number Theory*, Chapter VI.  Not in Mathlib v4.30. -/
def globalArtinMap_postulate
    (K : Type u) [Field K] [NumberField K]
    (L : Type u) [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsAbelianGalois K L] :
    IdeleGroup K →* (L ≃ₐ[K] L) := sorry

/-- **Postulate** (Artin reciprocity for the HCF):

The global Artin map applied to `J_K → Gal(H(K)/K)` factors through
`ClassGroup (𝓞 K)` (which is exactly the `artinReciprocity` field of
`HilbertClassFieldExt K`).

This is the BRIDGE between local (idele-based) and structural (class group)
formulations of CFT for HCF. -/
def globalArtinMap_factors_through_classGroup_postulate
    (K : Type u) [Field K] [NumberField K]
    (E : HilbertClassFieldExt K) :
    ∃ (φ : IdeleGroup K →* ClassGroup (𝓞 K)),
      (globalArtinMap_postulate K E.H : IdeleGroup K →* (E.H ≃ₐ[K] E.H))
        = E.artinReciprocity.toMonoidHom.comp φ := sorry

end NumberField
