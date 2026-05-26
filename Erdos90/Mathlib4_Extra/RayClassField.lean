/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Erdos90.Mathlib4_Extra.ClassFieldTheory

/-!
# Ray class fields and S-restricted extensions

The **ray class field** of a number field `K` modulo a modulus `𝔪` is the
maximal abelian extension `K(𝔪)/K` whose conductor divides `𝔪`.  This
generalizes the Hilbert class field (= ray class field with `𝔪 = 1`).

For the Hajir–Maire–Ramakrishna 2021 construction we need a related but
distinct object: the **maximal pro-`ℓ` extension unramified outside `S`**,
denoted `K_S^{(ℓ)}` or `K_S(F)` in HMR notation.  This is the union (= filtered
colimit) of finite abelian extensions `L/K` that are pro-`ℓ` (Galois group
is pro-`ℓ`) and unramified at every prime not in `S`.

## Why HMR uses S-restricted (not pure HCF) towers

The HCF tower (`K → H(K) → H(H(K)) → …`) has the property that each step is
*everywhere unramified*.  By Hilbert's theorem on principalization, every
ideal of `𝓞_K` becomes principal in `𝓞_{H(K)}`.  So if the HCF tower is
finite (=`K_n` is its own HCF), the *whole tower stabilizes* — i.e., the
HCF tower of `K` is finite iff `K` has finite class field tower.

Golod–Shafarevich (1964) showed that for fields with large enough class
group `p`-rank, the HCF tower is INFINITE.  This was the original
construction.

**But the everywhere-unramified condition is restrictive**: it requires
the class number to be growing, which is hard to control with `rd` bounded.

**HMR's improvement**: allow **tame** ramification at a fixed set `S` of
primes.  This relaxes the constraint, and via the **refined Golod–Shafarevich
criterion**, gives infinite towers with `rd ≤ 84` (much smaller than what
the pure HCF tower achieves).

The object underlying HMR is therefore `K_S^{(ℓ)}/K`, the maximal pro-`ℓ`
extension of `K` unramified outside `S` (where `S` includes primes above
`ℓ`).

## What this file provides

* `MaxProPExt K p S` — stub structure packaging the maximal pro-`p` extension
  unramified outside `S`.  Cite: HMR 2021 §2.
* `RayClassField K modulus` — stub for the classical ray class field.
* Documented relations to existing `HilbertClassFieldExt`.

## What's in Mathlib v4.30

Nothing.  No ray class field, no S-restricted maximal extensions.  See
`Erdos90/Mathlib4_Extra/ClassFieldTheory.lean` for the HCF stub which is
the simplest case.

## References

- HMR 2021 §2 of `assets/hmr_2021_src/Cutting_towers_arxiv.tex` (the
  refined GS construction).
- Neukirch, *Algebraic Number Theory*, Chapter VI for ray class fields.
- Koch, *Galois theory of p-extensions* for the pro-`p` extensions.
-/

namespace NumberField

universe u v

/-- **Maximal pro-`p` extension unramified outside `S`** (stub).

For a number field `K`, a prime `p`, and a finite set `S` of prime ideals
of `𝓞 K`, `MaxProPExt K p S` packages the existence of a (Galois) extension
`L/K` with the following properties:

* `Gal(L/K)` is a pro-`p` group.
* `L/K` is unramified at every prime of `𝓞 K` not in `S`.
* `L/K` is the maximal such extension.

This is HMR's `K_S^{(p)}` (or in their notation `K_S(F)`).

Note: in general `L/K` need not be a finite extension; this structure
captures it as a `Type` with a (potentially infinite) algebra structure.
The finite sub-extensions are then the "tower levels" used by GS. -/
structure MaxProPExt (K : Type u) [Field K] [NumberField K] (p : ℕ) (_S : Set (Ideal (𝓞 K))) where
  /-- The (potentially infinite) pro-`p` extension. -/
  L : Type v
  /-- `L` is a field. -/
  [fieldL : Field L]
  /-- `L` is an extension of `K`. -/
  [algebraKL : Algebra K L]
  /-- `L/K` is Galois (in the infinite Galois sense). -/
  [isGaloisKL : IsGalois K L]

attribute [instance] MaxProPExt.fieldL MaxProPExt.algebraKL MaxProPExt.isGaloisKL

/-- **Postulate** (Mathlib gap): the maximal pro-`p` extension `K_S^{(p)}` exists.

The pro-`p` Galois group `Gal(K_S^{(p)}/K)` is the *Galois cohomology object*
that GS criterion applies to.

Cite: Neukirch, *Cohomology of Number Fields*, Chapter X.  Not in Mathlib v4.30. -/
def maxProPExt_exists (K : Type u) [Field K] [NumberField K] (p : ℕ)
    (_hp : Nat.Prime p) (S : Set (Ideal (𝓞 K))) (_hS_fin : S.Finite) :
    MaxProPExt K p S := sorry

/-- **Ray class field** for a number field `K` and a modulus `𝔪` (stub).

The ray class field `K(𝔪)` is the maximal abelian extension of `K` whose
conductor divides `𝔪`.  When `𝔪 = 1`, this is the Hilbert class field.

Mathlib v4.30 doesn't have ray class groups or ray class fields.  This stub
documents the existence; closing it requires a full Mathlib formalization
of class field theory.

Cite: Neukirch, *Algebraic Number Theory*, Chapter VI §6. -/
structure RayClassField (K : Type u) [Field K] [NumberField K] (_𝔪 : Ideal (𝓞 K)) where
  /-- The ray class field type. -/
  Kmod : Type v
  /-- It's a field. -/
  [fieldKmod : Field Kmod]
  /-- It's a number field. -/
  [numberFieldKmod : NumberField Kmod]
  /-- It's an extension of `K`. -/
  [algebraK : Algebra K Kmod]
  /-- It's abelian Galois. -/
  [isAbelianGalois : IsAbelianGalois K Kmod]

attribute [instance] RayClassField.fieldKmod RayClassField.numberFieldKmod
  RayClassField.algebraK RayClassField.isAbelianGalois

/-- The Hilbert class field is the ray class field at modulus `1` (=`⊤`).

Specializing `RayClassField K ⊤` gives an extension that is also a
`HilbertClassFieldExt K` (modulo specific structure fields).  See HMR
2021 §2 for the connection. -/
def hcfFromRayClassField (K : Type u) [Field K] [NumberField K]
    (_R : RayClassField K ⊤) : Type _ := Unit  -- placeholder

end NumberField
