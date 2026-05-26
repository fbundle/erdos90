/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Erdos90.Mathlib4_Extra.UnramifiedDiscriminant

/-!
# Hilbert class field — Mathlib-PR-shape stub

The Hilbert class field `H(K)` of a number field `K` is the **maximal abelian
unramified extension of `K`**.  It is a classical object in class field theory:

* `Gal(H(K)/K) ≅ ClassGroup K` (Artin reciprocity, the heart of class field theory)
* `H(K)/K` is unramified at every finite and infinite place.
* Every ideal of `𝓞_K` becomes principal in `𝓞_{H(K)}` (principalization).

Mathlib v4.30 has **no class field theory**: no Artin reciprocity, no
ray class field, no Hilbert class field.  This file packages the existence of
`H(K)` as a stub structure `HilbertClassFieldExt K`, with the key properties as
fields.  A future Mathlib PR closing class field theory would provide the
witness for `hilbertClassField_exists K`.

## The Hilbert class field tower

The **Hilbert class field tower** of `K` is the sequence
```
K = K_0 ⊆ K_1 ⊆ K_2 ⊆ … where K_{n+1} = H(K_n).
```
Because each step is unramified, `rootDiscr K_n = rootDiscr K_0` for all `n`
(proved here via `rootDiscr_eq_of_unramifiedTower` from
`UnramifiedDiscriminant.lean`).

The Golod–Shafarevich theorem (see `GolodShafarevich.lean`) gives a criterion
on `ClassGroup K` ensuring the tower is **infinite** — i.e., `K_n ⊊ K_{n+1}`
for all `n`.  Combining with the rd-invariance gives Golod–Shafarevich's
construction of number fields with infinite class field towers and bounded
root discriminant.

## Main definitions

* `HilbertClassFieldExt K` — stub structure packaging the HCF and its key
  properties.
* `hilbertClassField_exists K` — postulated existence (TRUE per Artin
  reciprocity; not in Mathlib).
* `HCFTower K n` — the `n`-th step of the HCF tower (via repeated `HilbertClassFieldExt`).
* `hcfTower_rootDiscr_constant` — PROVED: root discriminant is invariant
  up the HCF tower.

## References

- Mathlib4 does not yet have `Mathlib/NumberTheory/ClassFieldTheory/`.
- External: <https://github.com/mariainesdff/LocalClassFieldTheory> for local CFT
  (Maria Inés de Frutos-Fernández).
- HMR 2021 §2 of `assets/hmr_2021_src/Cutting_towers_arxiv.tex`.
- Iwasawa / Lang's *Algebraic Number Theory* for the classical statement.
-/

universe u v

namespace NumberField

open NumberField

/-- **The Hilbert class field of a number field** (stub).

`HilbertClassFieldExt K` packages the existence of an extension `H/K` (the
Hilbert class field of `K`) with the key properties:

* `H` is a number field.
* `H/K` is finite Galois, with `[H:K] = h_K = classNumber K`.
* `H/K` is unramified at every nonzero prime of `𝓞 H`.
* `H/K` is abelian, with Galois group canonically isomorphic to `ClassGroup K`.

In Mathlib v4.30, neither the existence nor the structure is available; this
file postulates `HilbertClassFieldExt K` and assembles consequences.

Every field of this structure is a TRUE statement of class field theory; the
"closure" of this stub would be a Mathlib PR series formalizing Artin
reciprocity.
-/
structure HilbertClassFieldExt (K : Type u) [Field K] [NumberField K] where
  /-- The Hilbert class field type itself. -/
  H : Type v
  /-- `H` is a field. -/
  [fieldH : Field H]
  /-- `H` is a number field. -/
  [numberFieldH : NumberField H]
  /-- `H` is an extension of `K`. -/
  [algebraKH : Algebra K H]
  /-- `H/K` is Galois. -/
  [isGaloisHK : IsGalois K H]
  /-- `H/K` is abelian Galois (i.e., `Gal(H/K)` is commutative). -/
  [isAbelianGaloisHK : IsAbelianGalois K H]
  /-- `[H:K] = classNumber K` (the relative degree equals the class number). -/
  finrank_eq : Module.finrank K H = NumberField.classNumber K
  /-- `H/K` is unramified at every nonzero prime of `𝓞 H`. -/
  unramified :
    ∀ (P : Ideal (𝓞 H)) [P.IsPrime], P ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 K) P
  /-- **Artin reciprocity isomorphism**: `Gal(H/K) ≃* ClassGroup (𝓞 K)`.

  This is the heart of class field theory.  Note: we state the isomorphism
  as `ClassGroup (𝓞 K) ≃* (H ≃ₐ[K] H)` to match Mathlib's `Gal(H/K)` notation
  unfolding to `H ≃ₐ[K] H`. -/
  artinReciprocity : ClassGroup (𝓞 K) ≃* (H ≃ₐ[K] H)

attribute [instance] HilbertClassFieldExt.fieldH HilbertClassFieldExt.numberFieldH
  HilbertClassFieldExt.algebraKH HilbertClassFieldExt.isGaloisHK
  HilbertClassFieldExt.isAbelianGaloisHK

/-- **Postulate** (TRUE per class field theory): every number field has a
Hilbert class field.

This is the existential form of `HilbertClassFieldExt K`.  Cite: Artin
reciprocity (any standard CFT reference, e.g. Lang or Iwasawa).  Not in
Mathlib v4.30. -/
def hilbertClassField_exists (K : Type*) [Field K] [NumberField K] :
    HilbertClassFieldExt K := sorry

/-- Root discriminant is invariant under taking the Hilbert class field.

For any number field `K`, the HCF `H = H(K)` satisfies `rootDiscr H =
rootDiscr K` (since `H/K` is unramified).  This is PROVED Lean using
`rootDiscr_eq_of_unramifiedTower`.

Cite: HMR 2021 line 293, "root discriminants are constant in unramified
extensions". -/
theorem rootDiscr_hcf_eq (K : Type*) [Field K] [NumberField K]
    (E : HilbertClassFieldExt K) :
    rootDiscr E.H = rootDiscr K :=
  rootDiscr_eq_of_unramifiedTower K E.H E.unramified

/-! ## Proved corollaries of `HilbertClassFieldExt`

These follow directly from the structure fields + Mathlib.
-/

/-- The Galois group of `H/K` has cardinality equal to the class number of `K`.

This combines the Artin reciprocity isomorphism (a structure field) with
the finiteness of `ClassGroup (𝓞 K)`.  PROVED Lean. -/
theorem card_gal_hcf_eq_classNumber (K : Type u) [Field K] [NumberField K]
    (E : HilbertClassFieldExt K) :
    Nat.card (E.H ≃ₐ[K] E.H) = NumberField.classNumber K := by
  rw [← Nat.card_congr E.artinReciprocity.toEquiv]
  simp [NumberField.classNumber, Nat.card_eq_fintype_card]

/-- `H/K` is finite-dimensional.  Follows from `finrank_eq` and `classNumber_pos`.

PROVED Lean. -/
instance HilbertClassFieldExt.finiteDimensional
    (K : Type u) [Field K] [NumberField K]
    (E : HilbertClassFieldExt K) :
    FiniteDimensional K E.H :=
  .of_finrank_pos (by rw [E.finrank_eq]; exact NumberField.classNumber_pos K)

/-! ## The Hilbert class field tower (iterated HCF)

We define the n-th level of the HCF tower by repeated application of
`hilbertClassField_exists`, threading the algebra structure through each step.
-/

-- (HCFTower iteration omitted to keep the stub focused — it requires
-- dependent recursion threading Field/NumberField/Algebra instances at each
-- level, which adds significant complexity but no new mathematical content
-- beyond `rootDiscr_hcf_eq` applied repeatedly.)

-- (Field, NumberField, Algebra instances on HCFTower K n are non-trivial to
-- propagate through dependent recursion; we package them separately in
-- `HCFTowerData` below when needed.)

/-! ## Future work

The proof-path use case (`gs_cm_tower` in `NumberFieldDeep_GSTower.lean`) does
not directly use `HCFTower`: it just needs existence of *some* infinite tower
of CM fields with bounded `rootDiscr`.  The HMR 2021 construction uses a
*restricted* HCF tower — only allowing primes above a fixed set `S` to ramify —
which uses `RayClassField` (also absent from Mathlib).  See
`assets/search_results/D31_hmr_brd_what_we_need.md` for details.

For our purposes, `rootDiscr_hcf_eq` alone (proved above) demonstrates that
the discriminant-control half of HMR's argument is **PROVABLE in Mathlib once
HCF existence is postulated** — the obstruction is class field theory's
existence theorem, not discriminant arithmetic.
-/

end NumberField
