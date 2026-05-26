/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Erdos90.Mathlib4_Extra.LocalCFT

/-!
# Brauer group — Mathlib-PR-shape stub

The **Brauer group** `Br(K)` of a field `K` is the group of equivalence
classes of central simple algebras over `K`, with multiplication given by
tensor product.  Equivalently, `Br(K) ≅ H²(G_K, K^{sep,*})` (Galois
cohomology).

The Brauer group is a central object in class field theory:

* **Local CFT**: `Br(K_v) ≅ ℚ/ℤ` for non-archimedean `K_v` (the local
  invariant map).  This is the analytic content of local CFT.
* **Global CFT**: the **Hasse–Brauer–Noether sequence**
  `0 → Br(K) → ⊕_v Br(K_v) → ℚ/ℤ → 0`
  is exact, which gives local-to-global reciprocity.

## What's in Mathlib v4.30

Limited.  Mathlib has the **Picard group** (similar in spirit) and basic
Galois cohomology infrastructure, but no `BrauerGroup` as a unified object.

## What this file provides

Labelled stubs for:
* `BrauerGroup K` — `Br(K) ≅ H²(G_K, K^{sep,*})`.
* `localInvariantMap` — `Br(K_v) → ℚ/ℤ` for local fields.
* `hasseBrauerNoether` — the local-to-global exact sequence.

## References

- Serre, *Local Fields*, Chapter X.
- Neukirch, *Algebraic Number Theory*, Chapter VI §3.
- Milne's notes "Algebraic Number Theory" / "Class Field Theory".
-/

namespace NumberField

universe u

/-- **Brauer group** `Br(K)` of a field `K`.

Defined as `H²(G_K, K^{sep,*})` (Galois cohomology), this group classifies
central simple algebras over `K` modulo Morita equivalence.

Stub: Mathlib v4.30 doesn't have a unified `BrauerGroup` object. -/
def BrauerGroup (K : Type u) [Field K] : Type _ := Unit  -- placeholder

/-- **Local invariant map** (labelled postulate):

For a non-archimedean local field `K_v`, the Brauer group is isomorphic
to `ℚ/ℤ` via the local invariant map.

Cite: Serre *Local Fields* X §1.  Not in Mathlib v4.30. -/
def localInvariantMap_postulate
    (K : Type u) [Field K] :
    BrauerGroup K → ℚ := sorry

/-- **Hasse–Brauer–Noether theorem** (labelled postulate):

For a number field `K`, the sequence
  `0 → Br(K) → ⊕_v Br(K_v) → ℚ/ℤ → 0`
is exact, where the second map is the direct sum of local invariants and
the third is the sum.

This is the LOCAL-TO-GLOBAL principle for the Brauer group.  It implies
quadratic reciprocity (the sum of local Hilbert symbols is 0), the
Albert–Brauer–Hasse–Noether theorem on division algebras over number fields,
and is the analytic input for Tate's CFT proof.

Cite: Neukirch VI §3.  Not in Mathlib v4.30. -/
def hasseBrauerNoether_postulate
    (K : Type u) [Field K] [NumberField K] :
    True := sorry

end NumberField
