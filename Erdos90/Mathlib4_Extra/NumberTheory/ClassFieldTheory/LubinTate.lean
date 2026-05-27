/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Erdos90.Mathlib4_Extra.NumberTheory.ClassFieldTheory.LocalCFT

/-!
# Lubin–Tate formal groups — Mathlib-PR-shape stub

The **Lubin–Tate construction** (1965) gives an explicit construction of the
maximal abelian extension of a local field via formal group laws.

For a local field `K` (with residue field of cardinality `q = p^f`), choose
a uniformizer `π` and a "Lubin–Tate" polynomial `f(X) ∈ 𝓞_K[[X]]` with
`f(X) ≡ X^q (mod π)` and `f(X) ≡ πX (mod X^2)`.  The formal group law
constructed from `f` has its torsion points generating `K^{ab}`.

## Why it matters

Lubin–Tate gives:

1. An EXPLICIT construction of `K^{ab}` (not just an abstract existence).
2. An EXPLICIT local Artin map `K^* → Gal(K^{ab}/K)`.
3. A unified approach to ramified abelian extensions.

This is the foundation of LOCAL class field theory in its modern form.

## Mathlib v4.30 status

Frutos-Fernández's external `LocalClassFieldTheory` library has partial
Lubin-Tate.  Not in Mathlib core.

## What this file provides

Labelled stubs for:
* `LubinTateFormalGroup K π` — the formal group law.
* `lubinTate_torsion_postulate` — the torsion subgroup structure.
* `lubinTate_artin_map_postulate` — the explicit local Artin map.

## References

- Lubin–Tate, *Formal complex multiplication in local fields*, Ann. of Math. 81 (1965).
- Iwasawa, *Local Class Field Theory*, Chapter III.
- Serre, *Local Fields*, Chapter XIV (Lubin-Tate appendix).
-/

namespace NumberField

universe u

/-- **Lubin–Tate formal group** (labelled stub).

For a local field `K` and uniformizer `π`, the Lubin–Tate formal group is
constructed from any polynomial `f(X) ∈ 𝓞_K[[X]]` satisfying the Lubin-Tate
conditions.  Up to formal-group isomorphism, the group is independent of
the choice of `f`. -/
structure LubinTateFormalGroup (K : Type u) [Field K] (_π : K) where
  /-- The underlying formal group (stub). -/
  𝒢 : Unit

/-! ### Decomposition of Lubin-Tate construction

The Lubin-Tate construction (Lubin-Tate 1965) builds local CFT explicitly
via formal group laws.  The chain:

1. **Formal group law existence**: for each uniformizer π of a local
   field K, there exists a formal group F_π over 𝓞_K with [π]_F = π·X + X^q.
2. **Torsion field structure**: K_n = K(F_π[π^n]) is finite abelian over K
   with `[K_n : K] = q^{n-1}(q-1)`.
3. **Artin map**: the action of 𝓞_K^* on F_π-torsion gives the local Artin map.
4. **Maximality**: K_∞ = ∪K_n is the maximal totally ramified abelian
   extension of K.

Four sub-postulates below.
-/

/-- **Sub-postulate D3.local.lt.fg-existence** (Formal group existence):
For each uniformizer π of a non-archimedean local field K with residue
cardinality q, there exists a Lubin-Tate formal group law `F_π ∈ 𝓞_K[[X,Y]]`
with the linearization `[π]_F(X) ≡ πX (mod X²)` and `[π]_F(X) ≡ X^q (mod π)`.

Cite: Lubin-Tate 1965 §1; Iwasawa *Local CFT* Ch. 6.  Mathlib v4.30:
formal groups partially packaged; Lubin-Tate construction not. -/
def lubin_tate_formal_group_existence_postulate
    (K : Type u) [Field K] (π : K) : True := sorry

/-- **Sub-postulate D3.local.lt.torsion-degree** (Torsion field degree):
`K_n = K(F_π[π^n])` is finite abelian over K with `[K_n : K] = q^{n-1}(q-1)`,
where q is the residue cardinality of K.

Cite: Lubin-Tate 1965 §2.  Mathlib v4.30: not packaged. -/
def lubinTate_torsion_postulate
    (K : Type u) [Field K] (π : K) (_𝒢 : LubinTateFormalGroup K π) :
    True := sorry

/-- **Sub-postulate D3.local.lt.unit-action** (𝓞_K^* action on torsion):
The unit group 𝓞_K^* acts on F_π[π^n] by `u · v = [u]_F(v)` (where [u]_F is
the formal-group endomorphism associated to u), and this action is faithful
and transitive on primitive torsion points.

Cite: Lubin-Tate 1965 §3.  Mathlib v4.30: not packaged. -/
def lubin_tate_unit_action_postulate
    (K : Type u) [Field K] (π : K) (_𝒢 : LubinTateFormalGroup K π) :
    True := sorry

/-- **Postulate** (Lubin–Tate local Artin map):

The Lubin–Tate construction gives an explicit local Artin map
`K^* → Gal(K^{ab}/K)` that:
- Sends a uniformizer `π` to a "Frobenius lift" element fixing `K_n`.
- Sends `𝓞_K^*` to the inertia subgroup (corresponding to `K_∞ = ∪_n K_n`).

ASSEMBLY (modulo the three sub-postulates above):
1. By `lubin_tate_formal_group_existence_postulate`: F_π exists.
2. By `lubinTate_torsion_postulate`: K_n have the right degree.
3. By `lubin_tate_unit_action_postulate`: 𝓞_K^* acts via formal-group
   endomorphisms, giving inertia-to-Galois identification.
4. Compose with the π ↦ Frob choice to get the full local Artin map.

Cite: Lubin–Tate 1965; Iwasawa *Local Class Field Theory*. -/
def lubinTate_artin_map_postulate
    (K : Type u) [Field K] :
    True := sorry

end NumberField
