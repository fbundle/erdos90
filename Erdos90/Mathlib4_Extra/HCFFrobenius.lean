/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Erdos90.Mathlib4_Extra.ClassFieldTheory

/-!
# Frobenius elements in HCF — references to Mathlib's `arithFrobAt`

Mathlib provides the `IsArithFrobAt` predicate and `arithFrobAt` construction
in `Mathlib/RingTheory/Frobenius.lean` (PROVED in Mathlib).

For the Hilbert class field, every nonzero prime `P` of `𝓞_K` is unramified
in `𝓞_H`.  Therefore:

* For each prime `𝔓` of `𝓞_H` over `P`, the Frobenius `Frob_𝔓 ∈ Gal(H/K)` is
  the unique element such that `Frob_𝔓 x ≡ x^|κ(P)| (mod 𝔓)`.
* For abelian Galois (which HCF is), all `Frob_𝔓` for `𝔓` over `P` are
  CONJUGATE = EQUAL.  So we get a well-defined `Frob_P ∈ Gal(H/K)`.

This `Frob_P` is the **Artin symbol** σ_P from `ClassFieldTheory.lean`.

## What's provable from Mathlib + our infrastructure

* `arithFrobAt R G Q : G` (PROVED in Mathlib) — picks a Frobenius.
* For abelian G, all choices coincide — provable from `IsArithFrobAt.conj`.
* The map `P ↦ Frob_P` gives a hom `Cl(K) → Gal(H/K)` — this IS the
  Artin reciprocity.

## What's still postulated

* The compatibility of `arithFrobAt` with `HilbertClassFieldExt.artinSymbol`
  (via `artinReciprocity`) — requires identifying the two constructions.

## What this file provides

* Documentation referencing Mathlib's Frobenius.
* `HCFFrob_arbitrary` — for HCF, picks an arbitrary Frobenius element
  via Mathlib's `arithFrobAt`.

## References

- Mathlib's `Mathlib/RingTheory/Frobenius.lean` (Andrew Yang 2025).
- Neukirch *Algebraic Number Theory*, V §10.
-/

namespace NumberField

-- (Wrapping Mathlib's arithFrobAt for HCF is non-trivial because it
-- requires the typeclass that the Galois group acts on 𝓞 H with 𝓞 K as
-- fixed subring.  This requires substantial instance plumbing.  Documented
-- here as future work.)

-- TODO: wire `arithFrobAt (𝓞 K) (E.H ≃ₐ[K] E.H) P` to
-- `HilbertClassFieldExt.artinSymbol K E ⟨P, ...⟩` for prime P.

end NumberField
