/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Mathlib

/-!
# Galois cohomology — references to Mathlib + Mathlib4_Extra context

This file documents the parts of Galois cohomology that are ALREADY in
Mathlib v4.30, providing CFT-context for them.

Mathlib has substantial group cohomology infrastructure:
- `Mathlib/RepresentationTheory/Homological/GroupCohomology/Basic.lean`
- `Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`
- `Mathlib/RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean`
- `Mathlib/RepresentationTheory/Homological/GroupCohomology/Shapiro.lean`
- `Mathlib/RepresentationTheory/Homological/GroupCohomology/LongExactSequence.lean`
- `Mathlib/RepresentationTheory/Homological/GroupCohomology/FiniteCyclic.lean`

## Hilbert 90

Mathlib **PROVED** the classical Hilbert 90 (Noether's generalization):

  `H¹(Gal(L/K), L^*) = 0` for finite Galois extensions `L/K`.

Reference: `Mathlib/RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean`
declares `noncomputable instance H1ofAutOnUnitsUnique : Unique (H1 (Rep.ofAlgebraAutOnUnits K L))`.

This is one of the few CFT results that IS in Mathlib.

## Connection to CFT

Hilbert 90 is fundamental for:

1. **Local CFT**: helps prove that the local Artin map is well-defined.
2. **Global CFT**: foundational for `H²(K, K^*) = Br(K)` (the Brauer group).
3. **Norm theorems**: H¹ vanishing implies the norm exact sequence
   `1 → N_{L/K}(L^*) → K^* → K^* / N_{L/K}(L^*) → 1` is exact.

## What we're using

Our `Mathlib4_Extra/*` CFT stubs implicitly use Mathlib's H¹/H² infrastructure
via:
- `GolodShafarevich.lean`: GS test conditions on `H¹(G, 𝔽_p)` and `H²(G, 𝔽_p)`.
- `BrauerGroup.lean`: `Br(K) = H²(G_K, K^{sep,*})`.
- `LocalCFT.lean`: local Artin map via local cohomology.

When Mathlib's `GroupCohomology` is specialized to **pro-`p` Galois groups**
acting on `𝔽_p`, the GS criterion becomes directly applicable.

## Status

This file is documentation-only.  All references point to Mathlib's
PROVED infrastructure; nothing is sorried.
-/

namespace NumberField

-- (No new declarations.  This file documents the existing Mathlib
-- infrastructure that underlies our CFT stubs.)

end NumberField
