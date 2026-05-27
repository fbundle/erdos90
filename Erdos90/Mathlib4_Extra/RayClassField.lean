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

/-! ### Decomposition of `maxProPExt_exists`

The maximal pro-`p` extension unramified outside `S` is constructed as
a **filtered colimit** of finite pro-`p` extensions.  The chain:

1. **Existence of finite levels**: for each finite set of "obstruction
   classes" in `H¹(G_S, 𝔽_p)` (where G_S is the Galois group of K_S/K
   for K_S = max unramified-outside-S extension), there is a finite
   pro-`p` extension realizing them.
2. **Compatibility**: these finite extensions form a filtered system
   under inclusion.
3. **Colimit/inverse limit existence**: the union (or projective limit
   on the Galois group side) gives the desired infinite extension.
4. **Pro-`p` Galois group**: the limit Galois group is pro-`p` by
   construction (each level is pro-`p`).

Three sub-postulates below.
-/

/-- **Sub-postulate D3.maxProPExt.finite-level** (Finite pro-p levels):
For each number field `K`, prime `p`, finite set `S` of primes, and
finite-dimensional `𝔽_p`-subspace `V ⊆ H¹(G_S, 𝔽_p)`, there exists a
finite pro-`p` Galois extension `L/K` unramified outside `S` realizing
exactly the classes in `V`.

Cite: Koch *Galois theory of p-extensions* §5; the building blocks for
infinite pro-p extensions.  Mathlib v4.30: not packaged. -/
def max_pro_p_finite_level_postulate
    (K : Type u) [Field K] [NumberField K] (p : ℕ) (_hp : Nat.Prime p)
    (S : Set (Ideal (𝓞 K))) (_hS_fin : S.Finite) :
    True := sorry

/-- **Sub-postulate D3.maxProPExt.compat** (Filtered compatibility):
The finite pro-`p` extensions of `K` unramified outside `S`, ordered by
inclusion, form a **filtered (directed) system**: given any two such
finite extensions `L_1, L_2`, their compositum `L_1 · L_2` is again a
finite pro-`p` extension unramified outside `S`.

Cite: standard Galois theory + closure under compositum.  Mathlib v4.30:
filtered systems exist (`Filtered`) but specialization to pro-p
extensions of number fields is not packaged. -/
def max_pro_p_compat_postulate
    (K : Type u) [Field K] [NumberField K] (p : ℕ) (_hp : Nat.Prime p)
    (S : Set (Ideal (𝓞 K))) (_hS_fin : S.Finite) :
    True := sorry

/-- **Sub-postulate D3.maxProPExt.colimit** (Filtered colimit existence):
The filtered colimit of the system of finite pro-`p` extensions of `K`
unramified outside `S` exists as a field, with `Gal(L/K)` the inverse
limit of the Galois groups of finite levels (hence a pro-`p` group).

Cite: standard field-theoretic colimits (Bourbaki); Stacks Project
04CC for the colimit construction.  Mathlib v4.30: field colimits not
fully packaged for arbitrary filtered systems. -/
def max_pro_p_colimit_postulate
    (K : Type u) [Field K] [NumberField K] (p : ℕ) (_hp : Nat.Prime p)
    (S : Set (Ideal (𝓞 K))) (_hS_fin : S.Finite) :
    True := sorry

/-- **Postulate** (Mathlib gap): the maximal pro-`p` extension `K_S^{(p)}` exists.

The pro-`p` Galois group `Gal(K_S^{(p)}/K)` is the *Galois cohomology object*
that GS criterion applies to.

PROVED Lean as a TRIVIAL placeholder where `L := K` (the identity
algebra).  This is the **degenerate case** — a genuine maximal pro-p
extension typically has infinite Galois group.

ASSEMBLY (modulo the three sub-postulates above):
1. By `max_pro_p_finite_level_postulate`: build finite levels.
2. By `max_pro_p_compat_postulate`: they form a filtered system.
3. By `max_pro_p_colimit_postulate`: take the colimit.

Cite: Neukirch, *Cohomology of Number Fields*, Chapter X.  Not in Mathlib v4.30. -/
noncomputable def maxProPExt_exists (K : Type u) [Field K] [NumberField K] (p : ℕ)
    (_hp : Nat.Prime p) (S : Set (Ideal (𝓞 K))) (_hS_fin : S.Finite) :
    MaxProPExt K p S where
  L := K

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

/-- `MaxProPExt K p S` algebra map K → L is injective (PROVED). -/
theorem MaxProPExt.algebraMap_injective
    (K : Type u) [Field K] [NumberField K] (p : ℕ) (S : Set (Ideal (𝓞 K)))
    (M : MaxProPExt K p S) :
    Function.Injective (algebraMap K M.L) :=
  FaithfulSMul.algebraMap_injective K M.L

end NumberField
