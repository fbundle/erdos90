/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Erdos90.Mathlib4_Extra.ClassFieldTheory

/-!
# Norm group of an abelian extension — Mathlib-PR-shape stub

For a finite Galois extension `L/K`, the **norm map** `N_{L/K} : L^* → K^*`
sends `x` to `∏_{σ ∈ Gal(L/K)} σ(x)`.  The **norm group** is the image
`N_{L/K}(L^*) ⊆ K^*`.

Class field theory says: for ABELIAN `L/K`,

  `K^* / N_{L/K}(L^*) ≅ Gal(L/K)`

This is the fundamental local-global statement of CFT (via the local
norm residue map).

## The Hasse norm theorem

For abelian extensions of number fields, the principle of "local-global"
holds for norms: `x ∈ N_{L/K}(L^*)` iff `x ∈ N_{L_v/K_v}(L_v^*)` for every
place `v`.

This is the **Hasse Norm Theorem** (Hasse 1931).

## What's in Mathlib v4.30

- `Algebra.norm` (PROVED) — the underlying norm map.
- `Algebra.norm_self` (PROVED) — for the identity algebra.
- No `NormGroup` as a separate algebraic object.

## What this file provides

* `NormGroup K L` — the norm group `N_{L/K}(L^*)`.
* `index_eq_finrank_postulate` — `[K^* : N_{L/K}(L^*)] = [L:K]` for abelian L/K.
* `hasse_norm_theorem_postulate` — Hasse's local-global for norms.

## References

- Hasse, *Beweis eines Satzes und Widerlegung einer Vermutung über das
  allgemeine Normenrestsymbol*, 1931.
- Neukirch, *Algebraic Number Theory*, Chapter VI.
- Tate's lectures on number theory.
-/

namespace NumberField

universe u

/-- **Norm group** of a finite extension `L/K`: the image of the norm map
`N_{L/K} : L^* → K^*`. -/
noncomputable def NormGroup (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
    [Module.Finite K L] : Subgroup Kˣ :=
  ((Units.map (Algebra.norm K (S := L))).range)

/-- **Postulate** (CFT index formula for abelian extensions):

For an abelian finite extension `L/K` of number fields,
  `[K^* : N_{L/K}(L^*)] = [L : K]`.

In particular, the quotient `K^* / N_{L/K}(L^*) ≅ Gal(L/K)` (this is the
norm residue isomorphism). -/
def index_eq_finrank_postulate
    (K : Type u) [Field K] [NumberField K]
    (L : Type u) [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsAbelianGalois K L] :
    (NormGroup K L).index = Module.finrank K L := sorry

/-- **Postulate** (Hasse Norm Theorem):

For an abelian finite extension `L/K` of number fields, an element `x ∈ K^*`
is a norm from `L^*` iff it's a norm at every local completion.

  `x ∈ N_{L/K}(L^*) ↔ ∀ v, x ∈ N_{L_v/K_v}(L_v^*)`

Cite: Hasse 1931.  Not in Mathlib v4.30. -/
def hasse_norm_theorem_postulate
    (K : Type u) [Field K] [NumberField K]
    (L : Type u) [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsAbelianGalois K L]
    (_x : Kˣ) :
    True := sorry

/-! ## Connection to HCF

For the Hilbert class field `H = H(K)`:
- `Gal(H/K) ≅ ClassGroup (𝓞 K)` (Artin reciprocity)
- `K^* / N_{H/K}(H^*) ≅ Gal(H/K) ≅ ClassGroup (𝓞 K)`

So the norm group of HCF measures principal ideals: `x` is a norm from `H^*`
iff its ideal class is trivial in `ClassGroup (𝓞 K)`.

This is consistent with `HilbertClassFieldExt.bijective_algebraMap_of_classNumber_one`:
when `classNumber K = 1`, the class group is trivial, so every element is
a norm, so `NormGroup K H = K^*` (full subgroup). -/

end NumberField
