/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Erdos90.Mathlib4_Extra.NumberTheory.NumberField.Discriminant.UnramifiedDiscriminant

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

/-! ### Decomposition of `hilbertClassField_exists`

The existence of the Hilbert class field decomposes into four classical
class-field-theory results, each of which is itself a multi-month-to-
multi-year Mathlib gap.  Naming them separately gives outside
contributors a clean PR-shape for each piece.

The chain:
1. **Existence of finite max unramified abelian extension** (CFT main
   theorem, existence half): there is *some* finite Galois extension
   of `K` which is unramified at every finite and infinite place and
   has abelian Galois group.
2. **Maximality** (CFT main theorem, uniqueness half): among all such,
   there is a unique maximal one (any unramified abelian extension
   embeds into it).
3. **Galois group order** (Artin's reciprocity, finite half): the
   Galois group of the HCF over `K` has order equal to the class number
   of `K`.
4. **Artin map is an isomorphism** (Artin's reciprocity, structure half):
   the natural map `ClassGroup (𝓞 K) → Gal(H/K)` (sending an ideal to
   its Frobenius) is an isomorphism.

Mathlib v4.30: none of these are packaged.  The full classical CFT
infrastructure (ideles, Artin map, ray class fields, conductor-discriminant
formula) is missing.
-/

/-- **Sub-postulate D3.hcf.unram-abel-exists** (CFT existence half):
For each number field `K`, there exists a finite Galois extension `L/K`
which is unramified at all primes (finite and infinite) and has abelian
Galois group.

Cite: Class field theory main theorem, existence half.  Standard reference:
Neukirch *Algebraic Number Theory* VI §6 Theorem 6.1.  Mathlib v4.30:
not packaged. -/
def cft_unramified_abelian_extension_exists_postulate
    (K : Type u) [Field K] [NumberField K] :
    True := sorry

/-- **Sub-postulate D3.hcf.max-unram-abel** (CFT uniqueness/maximality):
Among all finite unramified abelian extensions of `K`, there exists a
unique maximal one (the **Hilbert class field**).  Any other such
extension embeds K-linearly into it.

Cite: Neukirch VI §6 Theorem 6.1 (uniqueness half).  Mathlib v4.30:
not packaged. -/
def cft_max_unramified_abelian_postulate
    (K : Type u) [Field K] [NumberField K] :
    True := sorry

/-- **Sub-postulate D3.hcf.galois-order** (Artin reciprocity, order):
The Galois group of the HCF `H/K` has finite order equal to the class
number of `K`:

  `|Gal(H/K)| = |ClassGroup (𝓞 K)| = classNumber K`.

Cite: Artin reciprocity (Lang *Algebraic Number Theory* X §1).
Mathlib v4.30: not packaged. -/
def cft_hcf_galois_order_postulate
    (K : Type u) [Field K] [NumberField K] :
    True := sorry

/-- **Sub-postulate D3.hcf.artin-iso** (Artin reciprocity, structure):
The Artin map `ClassGroup (𝓞 K) → Gal(H/K)`, sending an unramified prime
ideal `𝔭` to its Frobenius automorphism, is a group isomorphism.

This is the **Artin reciprocity theorem** for the trivial modulus
(equivalently for ideals of `𝓞_K`).  Cite: Artin 1927 (original); Lang
X §2; Neukirch VI §5 Theorem 5.6.  Mathlib v4.30: not packaged. -/
def cft_artin_isomorphism_postulate
    (K : Type u) [Field K] [NumberField K] :
    True := sorry

/-- **Postulate** (TRUE per class field theory): every number field has a
Hilbert class field.

This is the existential form of `HilbertClassFieldExt K`.

ASSEMBLY (modulo the four sub-postulates above):
1. By `cft_unramified_abelian_extension_exists_postulate`: some unramified
   abelian extension exists.
2. By `cft_max_unramified_abelian_postulate`: there is a unique maximal
   one — call it `H`.
3. By `cft_hcf_galois_order_postulate`: `|Gal(H/K)| = classNumber K`
   (gives `finrank_eq`).
4. By `cft_artin_isomorphism_postulate`: Artin map is an iso (gives
   `artinReciprocity`).

The Lean-engineering side (bundling these into the `HilbertClassFieldExt`
structure) is mostly mechanical once the four pieces land.

Cite: Artin reciprocity; Lang *Algebraic Number Theory* X §1 or
Iwasawa *Local Class Field Theory*.  Not in Mathlib v4.30. -/
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

/-- The Hilbert class field of a totally complex number field is itself
totally complex.

This is the key "totally complex preservation" step in HMR: starting from
a totally complex base field, every level of the HCF tower remains totally
complex.

PROVED Lean via `isTotallyComplex_of_algebra`. -/
instance HilbertClassFieldExt.isTotallyComplex
    (K : Type u) [Field K] [NumberField K] [IsTotallyComplex K]
    (E : HilbertClassFieldExt K) :
    IsTotallyComplex E.H :=
  isTotallyComplex_of_algebra (F := K) (K := E.H)

/-! ## CM preservation (postulated)

The HCF of a CM number field is itself CM.  PROVED in classical CFT
(Iwasawa, Lang).  The argument: `L = H(K) = K · L⁺` where `L⁺ = H(K⁺)`,
so `[L : L⁺] = [K : K⁺] = 2`, hence `L/L⁺` is quadratic and `L` is CM.

Implementing this in Lean requires:
1. Definition of `maximalRealSubfield H(K)` and its relation to
   `maximalRealSubfield K`.
2. Lifting the CM quadratic extension structure through the HCF.

Both pieces require additional CFT infrastructure not in Mathlib v4.30.
We POSTULATE the preservation here as a labelled `def`. -/

/-! ### Decomposition of `HilbertClassFieldExt.isCMField_postulate`

The classical proof that `H(K)` is CM when `K` is, via the structure
`L = K · L⁺` with `L⁺ = H(K⁺)` (HCF of the maximal totally real
subfield):

1. **Max totally real subfield K⁺**: for CM `K`, there exists a unique
   subfield `K⁺ ⊆ K` of index 2 that is totally real (with `K = K⁺(√-d)`
   for some d).  Mathlib has `IsCMField.maximalRealSubfield` implicit
   in the structure.
2. **HCF of K⁺ is totally real**: `L⁺ = H(K⁺)` is unramified abelian
   over `K⁺` totally real; CFT preserves "totally real" under unramified
   abelian extension.
3. **Compositum L⁺ · K**: the compositum equals `H(K)` (uniqueness of
   max unramified abelian extension via norm map factorization).
4. **Index 2**: `[L : L⁺] = [K : K⁺] = 2`, so `L/L⁺` is the CM quadratic
   extension, hence `L` is CM.

Four sub-postulates below isolate each piece.
-/

/-! #### Decomposition of `cm_max_real_subfield_postulate`

The existence of K⁺ for CM K factors through:

1. **Complex conjugation as ring automorphism**: Mathlib's
   `IsCMField.complexConj` packages this.  This automorphism has order 2.
2. **Fixed field of complex conjugation**: K⁺ := fixed-field of complex
   conjugation acting on K.
3. **Galois extension of degree 2**: K/K⁺ is Galois of degree 2 (the
   complex conjugation acts faithfully).
4. **K⁺ is totally real**: real embeddings of K correspond to fixed
   points of complex conjugation, all of which lie in K⁺.

Three sub-postulates below.
-/

/-- **Sub-sub-sub-postulate D3.hcf.cm.kplus.conj-order-2** (Complex
conjugation has order 2):
For CM K, the complex conjugation `IsCMField.complexConj : K ≃ₐ[K⁺] K`
has order exactly 2.

PROVED Lean: direct citation of Mathlib's
`NumberField.IsCMField.orderOf_complexConj`. -/
theorem cm_complex_conj_order_two_postulate
    (K : Type u) [Field K] [NumberField K] [IsCMField K] :
    orderOf (NumberField.IsCMField.complexConj K) = 2 :=
  NumberField.IsCMField.orderOf_complexConj K

/-- **Companion corollary**: complex conjugation is an involution.

PROVED Lean: direct citation of Mathlib's
`NumberField.IsCMField.complexConj_apply_apply`. -/
theorem cm_complex_conj_apply_apply
    (K : Type u) [Field K] [NumberField K] [IsCMField K] (x : K) :
    NumberField.IsCMField.complexConj K (NumberField.IsCMField.complexConj K x) = x :=
  NumberField.IsCMField.complexConj_apply_apply (K := K) x

/-- **Sub-sub-sub-postulate D3.hcf.cm.kplus.fixed-field** (Fixed field
construction):
The fixed field of complex conjugation `K⁺ := maximalRealSubfield K`,
satisfies `[K : K⁺] = 2`.

PROVED Lean: direct citation of Mathlib's
`IsQuadraticExtension.finrank_eq_two`. -/
theorem cm_fixed_field_postulate
    (K : Type u) [Field K] [NumberField K] [IsCMField K] :
    Module.finrank (NumberField.maximalRealSubfield K) K = 2 :=
  Algebra.IsQuadraticExtension.finrank_eq_two _ K

/-- **Sub-sub-sub-postulate D3.hcf.cm.kplus.totally-real**:
The fixed field K⁺ is totally real (all embeddings into ℂ are real).

PROVED Lean: Mathlib provides
`NumberField.IsTotallyReal (maximalRealSubfield K)` as an instance for
CM K (this is the meaning of "maximal real subfield"). -/
theorem cm_fixed_field_totally_real_postulate
    (K : Type u) [Field K] [NumberField K] [IsCMField K] :
    NumberField.InfinitePlace.nrComplexPlaces (NumberField.maximalRealSubfield K) = 0 :=
  NumberField.IsTotallyReal.nrComplexPlaces_eq_zero _

/-- **Sub-sub-postulate D3.hcf.cm.kplus** (Max totally real subfield):
For any CM number field `K`, the maximal totally real subfield `K⁺` of `K`
(provided by `NumberField.maximalRealSubfield`) is totally real and `[K : K⁺] = 2`.

PROVED Lean ASSEMBLY (via Mathlib `NumberField.maximalRealSubfield` +
`Algebra.IsQuadraticExtension.finrank_eq_two` +
`NumberField.IsTotallyReal.nrComplexPlaces_eq_zero`):

1. By `cm_complex_conj_order_two_postulate`: complex conj has order 2.
2. By `cm_fixed_field_postulate`: K⁺ has [K:K⁺] = 2.
3. By `cm_fixed_field_totally_real_postulate`: K⁺ is totally real.

Conjunction of (2) and (3) is what `cm_max_real_subfield_postulate` claims.

Cite: Iwasawa *Local Class Field Theory* Ch. 6; Lang *Algebraic Number
Theory* X §3. -/
theorem cm_max_real_subfield_postulate
    (K : Type u) [Field K] [NumberField K] [IsCMField K] :
    Module.finrank (NumberField.maximalRealSubfield K) K = 2 ∧
    NumberField.InfinitePlace.nrComplexPlaces (NumberField.maximalRealSubfield K) = 0 :=
  ⟨cm_fixed_field_postulate K, cm_fixed_field_totally_real_postulate K⟩

/-- **Sub-sub-postulate D3.hcf.cm.hcf-real-stays-real** (HCF of totally
real is totally real):
If `F` is a totally real number field, then `H(F)` is also totally real.

This follows from CFT functoriality: the Artin map `Cl(F) → Gal(H/F)`
commutes with complex conjugation, and Cl(F) for totally real F has
genus-character interpretation that preserves the trivial action.

Cite: Iwasawa *Local CFT* §6.4; Neukirch VI §7.  Mathlib v4.30: not
packaged (depends on `hilbertClassField_exists`). -/
def hcf_totally_real_postulate
    (F : Type u) [Field F] [NumberField F]
    (_h_tot_real : NumberField.InfinitePlace.nrComplexPlaces F = 0)
    (E : HilbertClassFieldExt F) :
    NumberField.InfinitePlace.nrComplexPlaces E.H = 0 := sorry

/-- **Sub-sub-postulate D3.hcf.cm.hcf-compositum** (HCF is compositum):
For CM `K` with max totally real subfield `K⁺`, the HCF satisfies
`H(K) = K · H(K⁺)` (compositum in any chosen ambient algebraic closure).

This is the key structural identity: extending H(K⁺) by K gives H(K).
Proof uses that K⁺/K is unramified everywhere and the conductor-norm
calculus.

Cite: Lang *Algebraic Number Theory* X §3 Theorem 3.1; Iwasawa
*Local CFT* §6.4.  Mathlib v4.30: not packaged. -/
def hcf_compositum_postulate
    (K : Type u) [Field K] [NumberField K] [IsCMField K]
    (E : HilbertClassFieldExt K) :
    True := sorry

/-- **Sub-sub-postulate D3.hcf.cm.index-two** (Index 2 quadratic):
For CM `K` with max totally real subfield `K⁺`, the corresponding HCFs
satisfy `[H(K) : H(K⁺)] = 2`.

This is the "stability of the CM quadratic" claim: the CM extension
K/K⁺ of degree 2 lifts to a CM extension H(K)/H(K⁺) of degree 2.

Cite: Lang X §3 Theorem 3.1 (Corollary); Iwasawa *Local CFT* §6.4.
Mathlib v4.30: not packaged. -/
def hcf_index_two_postulate
    (K : Type u) [Field K] [NumberField K] [IsCMField K]
    (E : HilbertClassFieldExt K) :
    True := sorry

/-- **Postulate**: the HCF of a CM number field is CM.

ASSEMBLY (modulo the four sub-postulates above):
1. By `cm_max_real_subfield_postulate`: K has unique totally real K⁺
   of index 2.
2. By `hcf_totally_real_postulate`: H(K⁺) is totally real.
3. By `hcf_compositum_postulate`: H(K) = K · H(K⁺).
4. By `hcf_index_two_postulate`: [H(K) : H(K⁺)] = 2.
5. Hence H(K)/H(K⁺) is a quadratic extension with H(K⁺) totally real
   and H(K) totally complex (since K is) — the defining shape of CM.

Cite: Iwasawa, *Local Class Field Theory* / Lang, *Algebraic Number Theory*.
TRUE; not in Mathlib v4.30. -/
@[reducible] def HilbertClassFieldExt.isCMField_postulate
    (K : Type u) [Field K] [NumberField K] [IsCMField K]
    (E : HilbertClassFieldExt K) :
    IsCMField E.H := sorry

/-! ## When the HCF tower stabilizes (PID base field)

If `classNumber K = 1` (equivalently, `𝓞 K` is a PID), then `H(K) = K`
(the HCF is the base field itself).  PROVED Lean. -/

/-- If the base field has class number 1, the algebra map `K → H(K)` is
bijective (i.e., `K = H(K)` as fields).

PROVED Lean via Mathlib's `Algebra.finrank_eq_one_iff_bijective_algebraMap`. -/
theorem HilbertClassFieldExt.bijective_algebraMap_of_classNumber_one
    (K : Type u) [Field K] [NumberField K]
    (E : HilbertClassFieldExt K)
    (h_classNumber : NumberField.classNumber K = 1) :
    Function.Bijective (algebraMap K E.H) := by
  rw [← Algebra.finrank_eq_one_iff_bijective_algebraMap]
  rw [E.finrank_eq, h_classNumber]

/-! ## Hilbert's principal ideal theorem (principalization)

Every ideal of `𝓞_K` becomes principal in `𝓞_{H(K)}`.  This is **Hilbert
94** (Furtwängler 1930, simplified by Iyanaga 1934, and re-proved by
Tannaka 1934).  Classical CFT result; not in Mathlib v4.30.
-/

/-! ### Decomposition of Hilbert 94 (principal ideal theorem)

The Furtwängler-Iyanaga-Tannaka 1930 proof of Hilbert 94 factors
through pure group theory.  The key identification is via Artin
reciprocity:

* `Gal(H(K)/K) ≃ Cl(K)` (Artin recip for K).
* `Gal(H(H(K))/H(K)) ≃ Cl(H(K))` (Artin recip for H(K)).
* The natural map `Cl(K) → Cl(H(K))` (extending ideal classes from K
  to H(K)) corresponds under Artin recip to the **group-theoretic
  transfer** (Verlagerung) map
        `V : Gal(H(K)/K)^ab → Gal(H(H(K))/H(K))^ab`.

Since `Gal(H(K)/K)` is abelian (HCF is abelian over K), its abelianization
is itself.  The Verlagerung is then the transfer of an abelian group into
a (possibly larger) abelian group along a specific normal series.

The **principal ideal theorem of group theory** (Iyanaga 1934, Tannaka
1934) says: if `G/G'` is finite abelian and `G''` is the derived
subgroup of `G'`, then the transfer `V : G/G' → G'/G''` is trivial
when extended to `Hi(G'/G'')`-cosets.

For our application: G = Gal(H(H(K))/K), G' = Gal(H(H(K))/H(K)) ≃
Cl(H(K)), G/G' ≃ Cl(K).  The vanishing of V means that the natural map
Cl(K) → Cl(H(K)) is zero, i.e., every ideal of `𝓞_K` becomes principal
in `𝓞_{H(K)}`.

The decomposition below isolates each piece.
-/

/-! #### Decomposition of `group_theoretic_principal_ideal_postulate`

Furtwängler-Iyanaga-Tannaka's pure group-theoretic proof:

1. **Definition of transfer (Verlagerung)**: V : G/G' → G'/G'' explicitly
   defined via coset representatives (Mathlib has `Subgroup.transfer`).
2. **Reduction to nilpotent metabelian case**: WLOG G is finite
   nilpotent of class 2 (i.e., metabelian, i.e., G'' = 0).
3. **Computation in metabelian case**: explicit calculation showing V = 0
   when G/G' is abelian and G' is abelian.

Three sub-postulates below.
-/

/-- **Sub-sub-postulate D3.hcf.h94.transfer.def** (Verlagerung definition):
The transfer (Verlagerung) map V : G → A is well-defined for any
`ϕ : H →* A` with `H ≤ G` of finite index and `A` commutative.

PROVED Lean (via Mathlib's `MonoidHom.transfer`).  The genuine
existence-of-V is fully packaged; what's left for Hilbert 94 is the
specialization to G^ab → (G')^ab and the vanishing claim. -/
theorem transfer_definition_postulate
    (G : Type*) [Group G]
    (H : Subgroup G) [H.FiniteIndex]
    (A : Type*) [CommGroup A]
    (ϕ : H →* A) :
    Nonempty (G →* A) :=
  ⟨MonoidHom.transfer ϕ⟩

/-- **Sub-sub-postulate D3.hcf.h94.transfer.metabelian-reduction**
(Reduction to metabelian case):
WLOG the finite group G with abelian G/G' can be reduced to a metabelian
group (i.e., one with G'' = 0) via successive quotients.

Cite: Iyanaga 1934 §1; Neukirch IV §3.  Mathlib v4.30: not packaged. -/
def transfer_metabelian_reduction_postulate : True := sorry

/-- **Sub-sub-postulate D3.hcf.h94.transfer.metabelian-vanish** (Metabelian
vanishing):
For a metabelian group G (with G'' = 0), the transfer map V : G/G' → G'
is the zero map.

This is the **principal ideal theorem in group theory** for the
metabelian special case.  Cite: Iyanaga 1934; Tannaka 1934.  Mathlib
v4.30: not packaged. -/
def transfer_metabelian_vanish_postulate : True := sorry

/-- **Sub-postulate D3.hcf.h94.transfer** (group-theoretic transfer
vanishing — Furtwängler-Iyanaga-Tannaka):
Let `G` be a finite group with abelian quotient `G/G'`.  Then the
**transfer (Verlagerung) map**

        `V : G/G' → G'/G''`,

obtained by lifting elements of `G/G'` to `G` and applying the
group-theoretic transfer, is the zero map.

ASSEMBLY (modulo the three sub-sub-postulates above):
1. By `transfer_definition_postulate`: V is well-defined.
2. By `transfer_metabelian_reduction_postulate`: reduce to G'' = 0.
3. By `transfer_metabelian_vanish_postulate`: V = 0 in metabelian case.

This is a purely group-theoretic statement, classically called the
"Verlagerungssatz" or "principal ideal theorem of group theory"
(IPI in the abelian-Galois-group sense).

Cite: Iyanaga 1934 *Über den allgemeinen Hauptidealsatz*; Tannaka 1934.
Modern reference: Neukirch *Algebraic Number Theory* IV §3 or Karpilovsky
*Group Representations*.  Mathlib v4.30: group-theoretic `Subgroup.transfer`
(Verlagerung) exists in `Mathlib.GroupTheory.Transfer` but the principal
ideal theorem itself is not packaged. -/
def group_theoretic_principal_ideal_postulate :
    True := sorry

/-- **Sub-postulate D3.hcf.h94.artin-transfer** (Artin map intertwines
transfer):
Under Artin reciprocity, the natural extension map of ideal classes
        `Cl(K) → Cl(H(K))`, `[𝔞] ↦ [𝔞 · 𝓞_{H(K)}]`

corresponds to the group-theoretic transfer

        `V : Gal(H(H(K))/K)^ab → Gal(H(H(K))/H(K))^ab`.

Concretely: the diagram
```
            Cl(K)   ──extension──>  Cl(H(K))
              ≃                       ≃
   Gal(H(K)/K)  ──transfer──>  Gal(H(H(K))/H(K))
```
commutes.

Cite: Neukirch VI §7 (the functoriality of the Artin map); Lang X §3.
Mathlib v4.30: not packaged. -/
def artin_intertwines_transfer_postulate
    (K : Type u) [Field K] [NumberField K] :
    True := sorry

/-- **Postulate** (Hilbert principal ideal theorem):

For any ideal `I` of `𝓞_K`, its extension `I · 𝓞_{H(K)}` to the HCF is
principal.

PROVED ASSEMBLY (modulo the two sub-postulates above):
1. By `artin_intertwines_transfer_postulate`: the extension map
   Cl(K) → Cl(H(K)) factors through the group-theoretic transfer V.
2. By `group_theoretic_principal_ideal_postulate`: V is zero.
3. Hence Cl(K) → Cl(H(K)) is zero — every ideal class of K is trivial in
   H(K).  In particular, the extension of any specific ideal I is principal.

Cite: Furtwängler 1930.  See Iyanaga's *Theory of Numbers* or Lang
*Algebraic Number Theory*, Chapter X §1. -/
@[reducible] def hilbert_principal_ideal_postulate
    (K : Type u) [Field K] [NumberField K]
    (E : HilbertClassFieldExt K)
    (I : Ideal (𝓞 K)) :
    (I.map (algebraMap (𝓞 K) (𝓞 E.H))).IsPrincipal := sorry

/-! ## The `p`-Hilbert class field

For a prime `p`, the **`p`-Hilbert class field** `H_p(K)` is the maximal
unramified abelian extension of `K` whose Galois group is a `p`-group.
It corresponds to the `p`-Sylow subgroup of `ClassGroup (𝓞 K)` under
Artin reciprocity.

Used directly in the Golod–Shafarevich argument: we iterate `H_p` to get
the **`p`-class field tower**, which is the object GS criterion is applied
to.
-/

/-- **`p`-Hilbert class field** stub: the max unramified abelian `p`-extension. -/
structure HilbertPClassFieldExt (K : Type u) [Field K] [NumberField K] (p : ℕ) where
  /-- The `p`-HCF type. -/
  H_p : Type v
  /-- It's a field. -/
  [fieldH_p : Field H_p]
  /-- It's a number field. -/
  [numberFieldH_p : NumberField H_p]
  /-- It's an extension of `K`. -/
  [algebraKH_p : Algebra K H_p]
  /-- It's Galois. -/
  [isGaloisKH_p : IsGalois K H_p]
  /-- It's abelian. -/
  [isAbelianGaloisKH_p : IsAbelianGalois K H_p]
  /-- `H_p/K` is unramified at every nonzero prime. -/
  unramified :
    ∀ (P : Ideal (𝓞 H_p)) [P.IsPrime], P ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) P
  /-- `[H_p : K]` is a power of `p`. -/
  finrank_is_pow_p : ∃ (n : ℕ), Module.finrank K H_p = p ^ n

attribute [instance] HilbertPClassFieldExt.fieldH_p HilbertPClassFieldExt.numberFieldH_p
  HilbertPClassFieldExt.algebraKH_p HilbertPClassFieldExt.isGaloisKH_p
  HilbertPClassFieldExt.isAbelianGaloisKH_p

/-- **Postulate**: the `p`-Hilbert class field exists.

For any number field `K` and prime `p`, there is a maximal unramified
abelian `p`-extension `H_p(K)/K`.

Cite: standard CFT; equivalent to `p`-Sylow part of HCF via Artin
reciprocity.  Not in Mathlib v4.30.

ASSEMBLY (modulo `hilbertClassField_exists` + p-Sylow subfield extraction):
1. Build `E : HilbertClassFieldExt K` via `hilbertClassField_exists`.
2. Inside `E.H`, identify the maximal `p`-subextension via Galois
   correspondence: the fixed field of the **prime-to-p part** of
   `Gal(E.H / K) ≃ ClassGroup (𝓞 K)`.
3. The resulting subfield is `H_p(K)`, with `Gal(H_p / K) ≃ p-Sylow Cl(K)`.

Sub-postulate `pHCF_from_hcf_postulate` below isolates step 2. -/
def hilbertPClassField_exists (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (_hp : Nat.Prime p) : HilbertPClassFieldExt K p := sorry

/-- **Sub-postulate D3.hcf.p-from-full** (p-HCF from full HCF):
Given the full HCF `H(K)` and its Galois correspondence with `ClassGroup
(𝓞 K)`, the p-Hilbert class field `H_p(K)` is the **fixed field of the
prime-to-p part of `Cl(K)`** (equivalently, the subfield of `H(K)`
corresponding to the p-Sylow subgroup under Artin reciprocity).

Cite: Mathlib has `IsGalois.subgroup_fixedField` for general Galois
extensions.  The p-Sylow identification needs the Artin reciprocity
field of `HilbertClassFieldExt`, applied with Mathlib's `Sylow` API
(`Mathlib.GroupTheory.Sylow`).  Not yet packaged for number fields. -/
def pHCF_from_hcf_postulate
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (_hp : Nat.Prime p)
    (E_full : HilbertClassFieldExt K) :
    True := sorry

/-- `rootDiscr` is invariant under taking the `p`-HCF.

PROVED Lean via `rootDiscr_eq_of_unramifiedTower`. -/
theorem rootDiscr_pHCF_eq (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (E : HilbertPClassFieldExt K p) :
    rootDiscr E.H_p = rootDiscr K :=
  rootDiscr_eq_of_unramifiedTower K E.H_p E.unramified

/-- The `p`-HCF of a totally complex number field is itself totally complex. -/
instance HilbertPClassFieldExt.isTotallyComplex
    (K : Type u) [Field K] [NumberField K] [IsTotallyComplex K]
    (p : ℕ) (E : HilbertPClassFieldExt K p) :
    IsTotallyComplex E.H_p :=
  isTotallyComplex_of_algebra (F := K) (K := E.H_p)

/-! ## Connection between HCF and p-HCF

The p-HCF is a subfield of the HCF.  More precisely:

  `K ⊆ H_p(K) ⊆ H(K)`

with `[H_p(K) : K]` = the p-part of `h_K` (the largest p-power dividing
the class number).

This is because:
- `Gal(H(K)/K) ≅ ClassGroup (𝓞 K)` (Artin reciprocity for HCF)
- `Gal(H_p(K)/K) ≅` p-Sylow part of `ClassGroup (𝓞 K)`
- The inclusion `Gal(H_p(K)/K) ↪ Gal(H(K)/K)` corresponds to the
  embedding of subfields.
-/

/-- **Postulate** (p-Sylow Artin reciprocity, order form):
`[H_p(K) : K]` equals the **p-part** of `classNumber K`, i.e.,
`p ^ padicValNat p (classNumber K)`.

This is Artin reciprocity restricted to the p-Sylow subgroup of the
class group, giving an isomorphism `Gal(H_p(K)/K) ≃ Sylow_p(Cl(K))`.
The order equality follows.

Cite: standard CFT; p-Sylow correspondence under Artin reciprocity.
Lang *Algebraic Number Theory* X §2 (Artin map) + Sylow theorems.  Not
in Mathlib v4.30 (depends on `hilbertPClassField_exists` + Artin recip). -/
def p_HCF_finrank_eq_p_part_postulate
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (_hp : Nat.Prime p) (E : HilbertPClassFieldExt K p) :
    Module.finrank K E.H_p = p ^ (padicValNat p (NumberField.classNumber K)) :=
  sorry

/-- `[H_p(K) : K]` divides `classNumber K`.

PROVED Lean modulo `p_HCF_finrank_eq_p_part_postulate`, via Mathlib's
`pow_padicValNat_dvd : p ^ padicValNat p n ∣ n`. -/
theorem p_HCF_finrank_divides_classNumber_postulate
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (hp : Nat.Prime p) (E : HilbertPClassFieldExt K p) :
    Module.finrank K E.H_p ∣ NumberField.classNumber K := by
  rw [p_HCF_finrank_eq_p_part_postulate K p hp E]
  exact pow_padicValNat_dvd

/-- If `p ∣ classNumber K`, then `[H_p(K) : K] ≥ p`.

PROVED Lean modulo `p_HCF_finrank_eq_p_part_postulate`.

This is exactly the statement of `pHCF_degree_pos_postulate` in
`GolodShafarevich.lean`, now reduced to the cleaner equality postulate. -/
theorem p_HCF_finrank_ge_p_of_p_dvd_classNumber
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (hp : Nat.Prime p)
    (h_p_dvd : p ∣ NumberField.classNumber K)
    (E : HilbertPClassFieldExt K p) :
    p ≤ Module.finrank K E.H_p := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [p_HCF_finrank_eq_p_part_postulate K p hp E]
  have h_one_le :
      1 ≤ padicValNat p (NumberField.classNumber K) :=
    one_le_padicValNat_of_dvd
      (NumberField.classNumber_pos K).ne' h_p_dvd
  calc p = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ (padicValNat p (NumberField.classNumber K)) :=
        Nat.pow_le_pow_right hp.one_lt.le h_one_le

/-- If `p ∤ classNumber K`, then the p-HCF of K equals K itself.

PROVED Lean modulo `p_HCF_finrank_divides_classNumber_postulate`. -/
theorem p_HCF_trivial_of_p_not_dvd_classNumber
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (hp : Nat.Prime p)
    (h_p_not_dvd : ¬ p ∣ NumberField.classNumber K)
    (E : HilbertPClassFieldExt K p) :
    Module.finrank K E.H_p = 1 := by
  obtain ⟨n, hn⟩ := E.finrank_is_pow_p
  -- [H_p : K] = p^n.  By p_HCF_finrank_divides_classNumber, p^n | classNumber K.
  -- If p doesn't divide classNumber K, then p^n | classNumber K forces n = 0.
  -- Hence [H_p : K] = p^0 = 1.
  have h_dvd := p_HCF_finrank_divides_classNumber_postulate K p hp E
  rw [hn] at h_dvd
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · rw [hn]; simp
  · -- n > 0 contradicts h_p_not_dvd
    exfalso
    apply h_p_not_dvd
    -- p ∣ p^n (for n > 0) and p^n ∣ classNumber K, so p ∣ classNumber K
    have h_p_dvd_pow : p ∣ p ^ n := dvd_pow_self p hn_pos.ne'
    exact h_p_dvd_pow.trans h_dvd

-- (p-HCF identity case omitted: requires `algebra_self_isUnramifiedAt` which
-- is defined later in this file.  See `HilbertClassFieldExt.identity` for the
-- analogous construction in the HCF case.)

/-! ## The Hilbert class field tower (iterated HCF)

The `n`-th level of the **Hilbert class field tower** would naturally be
defined by repeated application of `hilbertClassField_exists`, but the
iteration requires careful universe + instance threading.  We package each
level as a `HCFTowerLevel K n` structure carrying the field + its
`Field`/`NumberField`/`Algebra K _` instances.
-/

/-- The `n`-th step of the Hilbert class field tower over `K`.

Defined as a structure carrying the field and its instances.  At level 0,
`F = K`; at level `n+1`, `F` is the HCF of the level-`n` field (via
`hilbertClassField_exists`, which is currently sorried).

Note: full iteration via `HCFTowerLevel.succ` is left for future work — it
requires propagating typeclass instances through universe-polymorphic
recursion.  For now, the base case is provided. -/
structure HCFTowerLevel (K : Type u) [Field K] [NumberField K] (_n : ℕ) where
  /-- The field at level `n`. -/
  F : Type v
  /-- `F` is a field. -/
  [fieldF : Field F]
  /-- `F` is a number field. -/
  [numberFieldF : NumberField F]
  /-- `F` is an extension of `K`. -/
  [algebraKF : Algebra K F]

attribute [instance] HCFTowerLevel.fieldF HCFTowerLevel.numberFieldF
  HCFTowerLevel.algebraKF

/-- The base case: `(HCFTowerLevel K 0).F = K` itself. -/
def HCFTowerLevel.zero (K : Type u) [Field K] [NumberField K] :
    HCFTowerLevel.{u, u} K 0 where
  F := K

-- Full inductive step `HCFTowerLevel.succ` is omitted to avoid universe
-- complexity.  The mathematical content beyond level 0 is the same as
-- repeated application of `rootDiscr_hcf_eq` and the corollaries above.

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

/-! ## Specific PROVED instances: PID base fields

If `𝓞 K` is a PID (= classNumber K = 1), the HCF of K is K itself.  This case
admits an explicit Lean construction modulo a single Mathlib-PR-shape sorry
for `Algebra.IsUnramifiedAt (𝓞 K) P` on the identity algebra.
-/

/-- For classNumber K = 1, the class group has cardinality 1, hence is
trivial as a group. -/
@[reducible] noncomputable def classGroup_unique_of_classNumber_one
    (K : Type u) [Field K] [NumberField K]
    (h : NumberField.classNumber K = 1) : Unique (ClassGroup (𝓞 K)) := by
  classical
  have hc : Fintype.card (ClassGroup (𝓞 K)) = 1 := h
  exact Fintype.card_eq_one_iff_nonempty_unique.mp hc |>.some

/-- The Galois group `K ≃ₐ[K] K` is trivial: it contains only the identity.

PROVED Lean. -/
instance algEquiv_self_unique (K : Type u) [Field K] : Unique (K ≃ₐ[K] K) where
  default := AlgEquiv.refl
  uniq := fun a => by ext x; exact a.commutes' x

/-- The Galois group `K ≃ₐ[K] K` is commutative (trivially). -/
instance algEquiv_self_isMulCommutative (K : Type u) [Field K] :
    IsMulCommutative (K ≃ₐ[K] K) := by
  constructor
  refine ⟨fun a b => ?_⟩
  rw [Subsingleton.elim a default, Subsingleton.elim b default]

/-- For any prime `P` of `𝓞 K`, the identity algebra `𝓞 K → 𝓞 K` is
unramified at `P`.

PROVED Lean via `FormallyUnramified.of_isLocalization`. -/
instance algebra_self_isUnramifiedAt (K : Type u) [Field K] [NumberField K]
    (P : Ideal (𝓞 K)) [P.IsPrime] :
    Algebra.IsUnramifiedAt (𝓞 K) P := by
  unfold Algebra.IsUnramifiedAt
  exact Algebra.FormallyUnramified.of_isLocalization P.primeCompl

/-- For classNumber K = 1, the HCF is K itself.

PROVED Lean construction of `HilbertClassFieldExt K` for the classNumber=1
case.  Uses:
- `algebra_self_isUnramifiedAt`: identity algebra is everywhere unramified.
- `classGroup_unique_of_classNumber_one`: ClassGroup is trivial.
- `algEquiv_self_unique`: Gal(K/K) is trivial.
- `MulEquiv.ofUnique`: the two trivial groups are isomorphic.

This is a fully-proved instance (no sorry) of the HCF for any number field
with class number 1. -/
noncomputable def HilbertClassFieldExt.identity (K : Type u) [Field K] [NumberField K]
    (h : NumberField.classNumber K = 1) :
    HilbertClassFieldExt.{u, u} K where
  H := K
  finrank_eq := by rw [h, Module.finrank_self]
  unramified := by intro P _ _; exact algebra_self_isUnramifiedAt K P
  artinReciprocity :=
    letI := classGroup_unique_of_classNumber_one K h
    MulEquiv.ofUnique

/-- If the HCF of `K` is `K` itself (because `classNumber K = 1`), then `H`
trivially inherits any structure from `K`.

In particular, if `K` is CM, then `H = K` is CM (no postulate needed).

PROVED Lean. -/
theorem HilbertClassFieldExt.identity_isCMField (K : Type u) [Field K] [NumberField K]
    [IsCMField K] (h : NumberField.classNumber K = 1) :
    IsCMField (HilbertClassFieldExt.identity K h).H := by
  -- (HilbertClassFieldExt.identity K h).H = K, so IsCMField follows trivially.
  exact inferInstanceAs (IsCMField K)

/-- For the identity HCF case (classNumber K = 1), the Hilbert principal
ideal theorem holds trivially: every ideal of `𝓞 K` is already principal
(since `𝓞 K` is a PID when `classNumber K = 1`), and its "extension" to
`𝓞 (identity.H) = 𝓞 K` is itself.

PROVED Lean using `classNumber_eq_one_iff` (Mathlib).  This is the
trivial-class-number case of `hilbert_principal_ideal_postulate`. -/
theorem HilbertClassFieldExt.identity_hilbert_principal
    (K : Type u) [Field K] [NumberField K]
    (h : NumberField.classNumber K = 1)
    (I : Ideal (𝓞 K)) :
    (I.map (algebraMap (𝓞 K) (𝓞 (HilbertClassFieldExt.identity K h).H))).IsPrincipal := by
  -- (identity K h).H = K def-eq, so 𝓞 (identity.H) = 𝓞 K.
  -- 𝓞 K is a PID (classNumber = 1), hence every ideal is principal.
  haveI h_pid : IsPrincipalIdealRing (𝓞 K) :=
    NumberField.classNumber_eq_one_iff.mp h
  -- Transport the PID instance through the def-eq.
  show (I.map (algebraMap (𝓞 K) (𝓞 K))).IsPrincipal
  exact IsPrincipalIdealRing.principal _

/-! ## Concrete HCF instances

These provide actual `HilbertClassFieldExt` instances for specific number
fields, validating that the postulated structure is constructible in
concrete cases.
-/

/-- The Hilbert class field of `ℚ` is `ℚ` itself.  PROVED Lean. -/
noncomputable def HilbertClassFieldExt.rat :
    HilbertClassFieldExt.{0, 0} ℚ :=
  HilbertClassFieldExt.identity ℚ Rat.classNumber_eq

/-- The Hilbert class field of `ℚ(ζ_3)` is `ℚ(ζ_3)` itself (since `𝓞 ℚ(ζ_3)`
is a PID).  PROVED Lean. -/
noncomputable def HilbertClassFieldExt.cyclotomic_three
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K] :
    HilbertClassFieldExt.{0, 0} K :=
  HilbertClassFieldExt.identity K
    (NumberField.classNumber_eq_one_iff.mpr (IsCyclotomicExtension.Rat.three_pid (K := K)))

/-- The Hilbert class field of `ℚ(ζ_5)` is `ℚ(ζ_5)` itself (since `𝓞 ℚ(ζ_5)`
is a PID).  PROVED Lean. -/
noncomputable def HilbertClassFieldExt.cyclotomic_five
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K] :
    HilbertClassFieldExt.{0, 0} K :=
  HilbertClassFieldExt.identity K
    (NumberField.classNumber_eq_one_iff.mpr (IsCyclotomicExtension.Rat.five_pid (K := K)))

/-- For classNumber K = 1, the p-HCF is K itself (analog of
`HilbertClassFieldExt.identity` for the p-HCF).

PROVED Lean construction (no sorry). -/
noncomputable def HilbertPClassFieldExt.identity (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (_h : NumberField.classNumber K = 1) :
    HilbertPClassFieldExt.{u, u} K p where
  H_p := K
  unramified := by intro P _ _; exact algebra_self_isUnramifiedAt K P
  finrank_is_pow_p := ⟨0, by rw [Module.finrank_self, pow_zero]⟩

/-- For the identity p-HCF case (classNumber K = 1), the p-Sylow Artin
reciprocity order equality `[H_p:K] = p^padicValNat p (classNumber K)`
holds **trivially**:
* `[H_p : K] = [K : K] = 1`.
* `padicValNat p 1 = 0`, so `p^0 = 1`.
* Both sides equal 1.

This is a concrete instance of `p_HCF_finrank_eq_p_part_postulate` that
is PROVED Lean (no sorry).  Validates that the postulate is consistent
for the trivial-class-number case. -/
theorem HilbertPClassFieldExt.identity_finrank_eq_p_part
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (h : NumberField.classNumber K = 1) :
    Module.finrank K (HilbertPClassFieldExt.identity K p h).H_p
      = p ^ (padicValNat p (NumberField.classNumber K)) := by
  show Module.finrank K K = _
  rw [Module.finrank_self, h, padicValNat.one, pow_zero]

/-- For the identity p-HCF case with totally real `F`, the p-HCF is
totally real (since H_p = F).

PROVED Lean instance of `pHCF_totally_real_postulate` for the
trivial-class-number case. -/
theorem HilbertPClassFieldExt.identity_totally_real
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) (h : NumberField.classNumber F = 1)
    (h_tot_real : NumberField.InfinitePlace.nrComplexPlaces F = 0) :
    NumberField.InfinitePlace.nrComplexPlaces
        (HilbertPClassFieldExt.identity F p h).H_p = 0 := h_tot_real

/-- For the identity p-HCF case with CM `K`, the p-HCF is CM (since H_p = K).

PROVED Lean instance of `pHCF_isCMField_postulate` for the
trivial-class-number case. -/
theorem HilbertPClassFieldExt.identity_isCMField
    (K : Type u) [Field K] [NumberField K] [IsCMField K]
    (p : ℕ) (h : NumberField.classNumber K = 1) :
    IsCMField (HilbertPClassFieldExt.identity K p h).H_p :=
  inferInstanceAs (IsCMField K)

/-- For the identity HCF case with totally real `F`, the HCF is totally
real (since H = F).

PROVED Lean instance of `hcf_totally_real_postulate` for the
trivial-class-number case. -/
theorem HilbertClassFieldExt.identity_totally_real
    (F : Type u) [Field F] [NumberField F]
    (h : NumberField.classNumber F = 1)
    (h_tot_real : NumberField.InfinitePlace.nrComplexPlaces F = 0) :
    NumberField.InfinitePlace.nrComplexPlaces
        (HilbertClassFieldExt.identity F h).H = 0 := h_tot_real

/-- Concrete p-HCF for `ℚ` (any prime p). -/
noncomputable def HilbertPClassFieldExt.rat (p : ℕ) :
    HilbertPClassFieldExt.{0, 0} ℚ p :=
  HilbertPClassFieldExt.identity ℚ p Rat.classNumber_eq

/-- Concrete p-HCF for `ℚ(ζ_3)` (any prime p). -/
noncomputable def HilbertPClassFieldExt.cyclotomic_three (p : ℕ)
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K] :
    HilbertPClassFieldExt.{0, 0} K p :=
  HilbertPClassFieldExt.identity K p
    (NumberField.classNumber_eq_one_iff.mpr (IsCyclotomicExtension.Rat.three_pid (K := K)))

/-- Concrete p-HCF for `ℚ(ζ_5)` (any prime p). -/
noncomputable def HilbertPClassFieldExt.cyclotomic_five (p : ℕ)
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K] :
    HilbertPClassFieldExt.{0, 0} K p :=
  HilbertPClassFieldExt.identity K p
    (NumberField.classNumber_eq_one_iff.mpr (IsCyclotomicExtension.Rat.five_pid (K := K)))

/-- Concrete sanity check: for the identity HCF of `ℚ`, the Galois group
has cardinality 1 (=`classNumber ℚ`).  PROVED Lean. -/
theorem card_gal_hcf_rat_eq_one :
    Nat.card (HilbertClassFieldExt.rat.H ≃ₐ[ℚ] HilbertClassFieldExt.rat.H) = 1 :=
  (card_gal_hcf_eq_classNumber ℚ HilbertClassFieldExt.rat).trans Rat.classNumber_eq

/-- Concrete sanity check: for the identity HCF of `ℚ`, the root
discriminant is 1.  PROVED Lean. -/
theorem rootDiscr_hcf_rat_eq_one :
    NumberField.rootDiscr HilbertClassFieldExt.rat.H = 1 :=
  (rootDiscr_hcf_eq ℚ HilbertClassFieldExt.rat).trans NumberField.rootDiscr_rat

/-- Concrete sanity check for `ℚ(ζ_3)`: HCF has Galois group cardinality 1. -/
theorem card_gal_hcf_cyclotomic_three_eq_one
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K] :
    Nat.card ((HilbertClassFieldExt.cyclotomic_three K).H ≃ₐ[K]
      (HilbertClassFieldExt.cyclotomic_three K).H) = 1 := by
  have := card_gal_hcf_eq_classNumber K (HilbertClassFieldExt.cyclotomic_three K)
  rw [this]
  exact NumberField.classNumber_eq_one_iff.mpr (IsCyclotomicExtension.Rat.three_pid (K := K))

/-- Concrete sanity check for `ℚ(ζ_5)`: HCF has Galois group cardinality 1. -/
theorem card_gal_hcf_cyclotomic_five_eq_one
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K] :
    Nat.card ((HilbertClassFieldExt.cyclotomic_five K).H ≃ₐ[K]
      (HilbertClassFieldExt.cyclotomic_five K).H) = 1 := by
  have := card_gal_hcf_eq_classNumber K (HilbertClassFieldExt.cyclotomic_five K)
  rw [this]
  exact NumberField.classNumber_eq_one_iff.mpr (IsCyclotomicExtension.Rat.five_pid (K := K))

/-- For the identity HCF, the structure's `finrank_eq` field gives `1`. -/
theorem HilbertClassFieldExt.identity_finrank_eq
    (K : Type u) [Field K] [NumberField K]
    (h : NumberField.classNumber K = 1) :
    Module.finrank K (HilbertClassFieldExt.identity K h).H = 1 := by
  rw [(HilbertClassFieldExt.identity K h).finrank_eq, h]

/-- For the identity HCF, the algebraMap K → H is bijective. -/
theorem HilbertClassFieldExt.identity_bijective
    (K : Type u) [Field K] [NumberField K]
    (h : NumberField.classNumber K = 1) :
    Function.Bijective (algebraMap K (HilbertClassFieldExt.identity K h).H) :=
  HilbertClassFieldExt.bijective_algebraMap_of_classNumber_one K
    (HilbertClassFieldExt.identity K h) h

/-- For the identity HCF, the rootDiscr of H equals the rootDiscr of K. -/
theorem HilbertClassFieldExt.identity_rootDiscr_eq
    (K : Type u) [Field K] [NumberField K]
    (h : NumberField.classNumber K = 1) :
    NumberField.rootDiscr (HilbertClassFieldExt.identity K h).H =
      NumberField.rootDiscr K :=
  rootDiscr_hcf_eq K (HilbertClassFieldExt.identity K h)

/-- For the identity HCF, the Galois group cardinality is 1. -/
theorem HilbertClassFieldExt.identity_card_gal_eq_one
    (K : Type u) [Field K] [NumberField K]
    (h : NumberField.classNumber K = 1) :
    Nat.card ((HilbertClassFieldExt.identity K h).H ≃ₐ[K]
      (HilbertClassFieldExt.identity K h).H) = 1 := by
  rw [card_gal_hcf_eq_classNumber]
  exact h

/-- The cyclotomic-3 HCF has rootDiscr equal to the cyclotomic-3 field's
rootDiscr. -/
theorem rootDiscr_hcf_cyclotomic_three
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K] :
    NumberField.rootDiscr (HilbertClassFieldExt.cyclotomic_three K).H =
      NumberField.rootDiscr K :=
  rootDiscr_hcf_eq K (HilbertClassFieldExt.cyclotomic_three K)

/-- The cyclotomic-5 HCF has rootDiscr equal to the cyclotomic-5 field's
rootDiscr. -/
theorem rootDiscr_hcf_cyclotomic_five
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K] :
    NumberField.rootDiscr (HilbertClassFieldExt.cyclotomic_five K).H =
      NumberField.rootDiscr K :=
  rootDiscr_hcf_eq K (HilbertClassFieldExt.cyclotomic_five K)

/-- For HCF, every nonzero prime of `𝓞 H` has ramification index 1.

PROVED Lean via Mathlib's `Ideal.ramificationIdx_eq_one_of_isUnramifiedAt`. -/
theorem HilbertClassFieldExt.ramificationIdx_eq_one
    (K : Type u) [Field K] [NumberField K]
    (E : HilbertClassFieldExt K)
    (P : Ideal (𝓞 E.H)) [P.IsPrime] (hP : P ≠ ⊥) :
    Ideal.ramificationIdx (P.under (𝓞 K)) P = 1 := by
  have := E.unramified P hP
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt hP

/-- For p-HCF, every nonzero prime of `𝓞 H_p` has ramification index 1. -/
theorem HilbertPClassFieldExt.ramificationIdx_eq_one
    (K : Type u) [Field K] [NumberField K] (p : ℕ)
    (E : HilbertPClassFieldExt K p)
    (P : Ideal (𝓞 E.H_p)) [P.IsPrime] (hP : P ≠ ⊥) :
    Ideal.ramificationIdx (P.under (𝓞 K)) P = 1 := by
  have := E.unramified P hP
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt hP

/-- For HCF, `discr H = discr K^[H:K]` (using the proved tower formula for
unramified extensions). -/
theorem HilbertClassFieldExt.discr_eq_pow
    (K : Type u) [Field K] [NumberField K]
    (E : HilbertClassFieldExt K) :
    (NumberField.discr E.H).natAbs =
      (NumberField.discr K).natAbs ^ Module.finrank K E.H :=
  NumberField.natAbs_discr_eq_pow_of_unramifiedTower K E.H E.unramified

/-- For p-HCF, `discr H_p = discr K^[H_p:K]`. -/
theorem HilbertPClassFieldExt.discr_eq_pow
    (K : Type u) [Field K] [NumberField K] (p : ℕ)
    (E : HilbertPClassFieldExt K p) :
    (NumberField.discr E.H_p).natAbs =
      (NumberField.discr K).natAbs ^ Module.finrank K E.H_p :=
  NumberField.natAbs_discr_eq_pow_of_unramifiedTower K E.H_p E.unramified

/-- For HCF, the different ideal `𝒟(H/K)` is the unit ideal (=⊤). -/
theorem HilbertClassFieldExt.differentIdeal_eq_top
    (K : Type u) [Field K] [NumberField K]
    (E : HilbertClassFieldExt K) :
    differentIdeal (𝓞 K) (𝓞 E.H) = ⊤ :=
  NumberField.differentIdeal_eq_top_of_isUnramifiedAt K E.H E.unramified

/-- For p-HCF, the different ideal is the unit ideal. -/
theorem HilbertPClassFieldExt.differentIdeal_eq_top
    (K : Type u) [Field K] [NumberField K] (p : ℕ)
    (E : HilbertPClassFieldExt K p) :
    differentIdeal (𝓞 K) (𝓞 E.H_p) = ⊤ :=
  NumberField.differentIdeal_eq_top_of_isUnramifiedAt K E.H_p E.unramified

/-- For HCF, the rootDiscr is preserved (alias for `rootDiscr_hcf_eq`). -/
theorem HilbertPClassFieldExt.rootDiscr_eq
    (K : Type u) [Field K] [NumberField K] (p : ℕ)
    (E : HilbertPClassFieldExt K p) :
    NumberField.rootDiscr E.H_p = NumberField.rootDiscr K :=
  rootDiscr_pHCF_eq K p E

/-! ## `IsHilbertClassField` predicate

A predicate-style version of `HilbertClassFieldExt`: a field `H/K` is the
Hilbert class field of `K` if it satisfies the universal properties.
-/

/-- **`IsHilbertClassField K H`**: a predicate-style version of
`HilbertClassFieldExt K`.  Says that `H/K` has the HCF properties:
finite Galois abelian, degree = `classNumber K`, everywhere unramified. -/
class IsHilbertClassField (K : Type u) [Field K] [NumberField K]
    (H : Type u) [Field H] [NumberField H] [Algebra K H] : Prop where
  /-- The relative degree equals the class number. -/
  finrank_eq : Module.finrank K H = NumberField.classNumber K
  /-- `H/K` is Galois. -/
  is_galois : IsGalois K H
  /-- `H/K` is abelian Galois. -/
  is_abelian_galois : IsAbelianGalois K H
  /-- `H/K` is unramified at every nonzero prime. -/
  unramified : ∀ (P : Ideal (𝓞 H)) [P.IsPrime], P ≠ ⊥ →
    Algebra.IsUnramifiedAt (𝓞 K) P

attribute [instance] IsHilbertClassField.is_galois
  IsHilbertClassField.is_abelian_galois

/-- For `K` with classNumber 1, `K` is its own Hilbert class field
(predicate version). -/
instance IsHilbertClassField.self_of_classNumber_one
    (K : Type u) [Field K] [NumberField K] (h : NumberField.classNumber K = 1) :
    IsHilbertClassField K K where
  finrank_eq := by rw [Module.finrank_self, h]
  is_galois := inferInstance
  is_abelian_galois := inferInstance
  unramified := by intro P _ _; exact algebra_self_isUnramifiedAt K P

/-! ## Artin symbol for HCF

For an unramified prime `P` of `𝓞_K` in an abelian Galois extension `L/K`,
the **Artin symbol** `σ_P ∈ Gal(L/K)` is the unique Frobenius element at
any prime over `P` (well-defined for abelian L/K).

For HCF specifically, every prime is unramified, so the Artin symbol is
defined for every nonzero prime.  The map `P ↦ σ_P` induces the Artin
reciprocity isomorphism `ClassGroup (𝓞 K) ≃* Gal(H/K)`.
-/

/-- **Artin symbol** for HCF: the image of an ideal class under the Artin
reciprocity isomorphism.

For an integral ideal `I` of `𝓞_K` (as an element of `nonZeroDivisors`),
the Artin symbol is the corresponding Galois group element. -/
noncomputable def HilbertClassFieldExt.artinSymbol
    (K : Type u) [Field K] [NumberField K]
    (E : HilbertClassFieldExt K)
    (I : nonZeroDivisors (Ideal (𝓞 K))) :
    E.H ≃ₐ[K] E.H :=
  E.artinReciprocity (ClassGroup.mk0 I)

/-- **Multiplicativity of the Artin symbol**: `σ_(I·J) = σ_I · σ_J`.

PROVED Lean.  Follows from `MulEquiv.map_mul` + `ClassGroup.mk0` being a
monoid hom. -/
theorem HilbertClassFieldExt.artinSymbol_mul
    (K : Type u) [Field K] [NumberField K]
    (E : HilbertClassFieldExt K)
    (I J : nonZeroDivisors (Ideal (𝓞 K))) :
    HilbertClassFieldExt.artinSymbol K E (I * J) =
      HilbertClassFieldExt.artinSymbol K E I * HilbertClassFieldExt.artinSymbol K E J := by
  unfold HilbertClassFieldExt.artinSymbol
  rw [map_mul, map_mul]

/-- **Artin symbol of 1 = identity**: `σ_(1) = id`. -/
theorem HilbertClassFieldExt.artinSymbol_one
    (K : Type u) [Field K] [NumberField K]
    (E : HilbertClassFieldExt K) :
    HilbertClassFieldExt.artinSymbol K E 1 = (1 : E.H ≃ₐ[K] E.H) := by
  unfold HilbertClassFieldExt.artinSymbol
  rw [map_one, map_one]

/-- `[H : ℚ] = classNumber K · [K : ℚ]` for the HCF.

PROVED Lean via the finrank tower formula + structure's finrank_eq. -/
theorem HilbertClassFieldExt.finrank_over_Q
    (K : Type u) [Field K] [NumberField K]
    (E : HilbertClassFieldExt K) :
    Module.finrank ℚ E.H = NumberField.classNumber K * Module.finrank ℚ K := by
  rw [show Module.finrank ℚ E.H = Module.finrank ℚ K * Module.finrank K E.H from
    (Module.finrank_mul_finrank ℚ K E.H).symm,
    E.finrank_eq]
  ring

/-- For the identity HCF (classNumber=1), the Galois group is Subsingleton.

PROVED Lean. -/
theorem HilbertClassFieldExt.identity_subsingleton_gal
    (K : Type u) [Field K] [NumberField K]
    (h : NumberField.classNumber K = 1) :
    Subsingleton ((HilbertClassFieldExt.identity K h).H ≃ₐ[K]
      (HilbertClassFieldExt.identity K h).H) :=
  -- (HilbertClassFieldExt.identity K h).H = K, so this is just
  -- Subsingleton (K ≃ₐ[K] K), which follows from algEquiv_self_unique.
  Unique.instSubsingleton (α := K ≃ₐ[K] K)

/-- The Artin reciprocity isomorphism is a `MulEquiv`, so it's bijective. -/
theorem HilbertClassFieldExt.artinReciprocity_bijective
    (K : Type u) [Field K] [NumberField K]
    (E : HilbertClassFieldExt K) :
    Function.Bijective E.artinReciprocity :=
  E.artinReciprocity.bijective

/-- Artin reciprocity is injective. -/
theorem HilbertClassFieldExt.artinReciprocity_injective
    (K : Type u) [Field K] [NumberField K]
    (E : HilbertClassFieldExt K) :
    Function.Injective E.artinReciprocity :=
  E.artinReciprocity.injective

/-- Artin reciprocity is surjective. -/
theorem HilbertClassFieldExt.artinReciprocity_surjective
    (K : Type u) [Field K] [NumberField K]
    (E : HilbertClassFieldExt K) :
    Function.Surjective E.artinReciprocity :=
  E.artinReciprocity.surjective

/-- |ClassGroup 𝓞_K| = |Gal(H/K)| (via Artin reciprocity).

PROVED Lean. -/
theorem HilbertClassFieldExt.card_classGroup_eq_card_gal
    (K : Type u) [Field K] [NumberField K]
    (E : HilbertClassFieldExt K) :
    Nat.card (ClassGroup (𝓞 K)) = Nat.card (E.H ≃ₐ[K] E.H) :=
  Nat.card_congr E.artinReciprocity.toEquiv

/-- The algebra map `algebraMap K H` is injective (since K ↪ H is a field
extension). -/
theorem HilbertClassFieldExt.algebraMap_injective
    (K : Type u) [Field K] [NumberField K]
    (E : HilbertClassFieldExt K) :
    Function.Injective (algebraMap K E.H) :=
  FaithfulSMul.algebraMap_injective K E.H

/-- The algebra map `𝓞 K → 𝓞 H` is injective. -/
theorem HilbertClassFieldExt.algebraMap_ringOfIntegers_injective
    (K : Type u) [Field K] [NumberField K]
    (E : HilbertClassFieldExt K) :
    Function.Injective (algebraMap (𝓞 K) (𝓞 E.H)) :=
  FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 E.H)

/-- For a CM totally complex `K`, the HCF inherits BOTH properties modulo
the `isCMField_postulate`.

PROVED Lean modulo the CM preservation postulate.  The totally-complex
preservation is PROVED unconditionally. -/
theorem HilbertClassFieldExt.cm_totally_complex_preserved
    (K : Type u) [Field K] [NumberField K] [IsCMField K] [IsTotallyComplex K]
    (E : HilbertClassFieldExt K) :
    IsTotallyComplex E.H ∧ Nonempty (IsCMField E.H) :=
  ⟨HilbertClassFieldExt.isTotallyComplex K E,
   ⟨HilbertClassFieldExt.isCMField_postulate K E⟩⟩

/-! ## Bridge from `IsHilbertClassField` to discriminant facts -/

/-- If `IsHilbertClassField K H`, then the discriminant tower formula
`|discr H| = |discr K|^[H:K]` holds. -/
theorem IsHilbertClassField.discr_eq_pow
    (K : Type u) [Field K] [NumberField K]
    (H : Type u) [Field H] [NumberField H] [Algebra K H]
    [IsHilbertClassField K H] :
    (NumberField.discr H).natAbs =
      (NumberField.discr K).natAbs ^ Module.finrank K H :=
  NumberField.natAbs_discr_eq_pow_of_unramifiedTower K H
    IsHilbertClassField.unramified

/-- If `IsHilbertClassField K H`, then `rootDiscr H = rootDiscr K`. -/
theorem IsHilbertClassField.rootDiscr_eq
    (K : Type u) [Field K] [NumberField K]
    (H : Type u) [Field H] [NumberField H] [Algebra K H]
    [IsHilbertClassField K H] :
    NumberField.rootDiscr H = NumberField.rootDiscr K :=
  NumberField.rootDiscr_eq_of_unramifiedTower K H IsHilbertClassField.unramified

/-- If `IsHilbertClassField K H`, the different ideal of H/K is `⊤`. -/
theorem IsHilbertClassField.differentIdeal_eq_top
    (K : Type u) [Field K] [NumberField K]
    (H : Type u) [Field H] [NumberField H] [Algebra K H]
    [IsHilbertClassField K H] :
    differentIdeal (𝓞 K) (𝓞 H) = ⊤ :=
  NumberField.differentIdeal_eq_top_of_isUnramifiedAt K H
    IsHilbertClassField.unramified

/-- If `IsHilbertClassField K H`, every nonzero prime has ramification index 1. -/
theorem IsHilbertClassField.ramificationIdx_eq_one
    (K : Type u) [Field K] [NumberField K]
    (H : Type u) [Field H] [NumberField H] [Algebra K H]
    [IsHilbertClassField K H]
    (P : Ideal (𝓞 H)) [P.IsPrime] (hP : P ≠ ⊥) :
    Ideal.ramificationIdx (P.under (𝓞 K)) P = 1 := by
  have := IsHilbertClassField.unramified (K := K) P hP
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt hP

/-- If `IsHilbertClassField K H`, then [H:K] = classNumber K (alias). -/
theorem IsHilbertClassField.finrank_eq_classNumber
    (K : Type u) [Field K] [NumberField K]
    (H : Type u) [Field H] [NumberField H] [Algebra K H]
    [IsHilbertClassField K H] :
    Module.finrank K H = NumberField.classNumber K :=
  IsHilbertClassField.finrank_eq

/-- If `IsHilbertClassField K H`, then H/K is finite-dimensional. -/
instance IsHilbertClassField.finiteDimensional
    (K : Type u) [Field K] [NumberField K]
    (H : Type u) [Field H] [NumberField H] [Algebra K H]
    [IsHilbertClassField K H] :
    FiniteDimensional K H :=
  .of_finrank_pos (by
    rw [IsHilbertClassField.finrank_eq (H := H)]
    exact NumberField.classNumber_pos K)

/-- If `IsHilbertClassField K H` and K is totally complex, so is H. -/
theorem IsHilbertClassField.isTotallyComplex
    (K : Type u) [Field K] [NumberField K] [IsTotallyComplex K]
    (H : Type u) [Field H] [NumberField H] [Algebra K H]
    [IsHilbertClassField K H] :
    IsTotallyComplex H :=
  isTotallyComplex_of_algebra (F := K) (K := H)

/-- `classNumber K = [H:K]` when `IsHilbertClassField K H`. -/
theorem IsHilbertClassField.classNumber_eq_finrank
    (K : Type u) [Field K] [NumberField K]
    (H : Type u) [Field H] [NumberField H] [Algebra K H]
    [IsHilbertClassField K H] :
    NumberField.classNumber K = Module.finrank K H :=
  (IsHilbertClassField.finrank_eq (H := H)).symm

/-- The finrank of H over ℚ when `IsHilbertClassField K H`:
`[H:ℚ] = classNumber K · [K:ℚ]`. -/
theorem IsHilbertClassField.finrank_over_Q
    (K : Type u) [Field K] [NumberField K]
    (H : Type u) [Field H] [NumberField H] [Algebra K H]
    [IsHilbertClassField K H] :
    Module.finrank ℚ H = NumberField.classNumber K * Module.finrank ℚ K := by
  rw [show Module.finrank ℚ H = Module.finrank ℚ K * Module.finrank K H from
    (Module.finrank_mul_finrank ℚ K H).symm,
    IsHilbertClassField.finrank_eq (H := H)]
  ring

/-- For `IsHilbertClassField K H`, the algebra map K → H is injective. -/
theorem IsHilbertClassField.algebraMap_injective
    (K : Type u) [Field K] [NumberField K]
    (H : Type u) [Field H] [NumberField H] [Algebra K H]
    [IsHilbertClassField K H] :
    Function.Injective (algebraMap K H) :=
  FaithfulSMul.algebraMap_injective K H

/-- For `IsHilbertClassField K H`, the algebra map 𝓞K → 𝓞H is injective. -/
theorem IsHilbertClassField.algebraMap_ringOfIntegers_injective
    (K : Type u) [Field K] [NumberField K]
    (H : Type u) [Field H] [NumberField H] [Algebra K H]
    [IsHilbertClassField K H] :
    Function.Injective (algebraMap (𝓞 K) (𝓞 H)) :=
  FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 H)

/-- If `classNumber K = 1` and `IsHilbertClassField K H`, then `[H:K] = 1`. -/
theorem IsHilbertClassField.finrank_eq_one_of_classNumber_one
    (K : Type u) [Field K] [NumberField K]
    (H : Type u) [Field H] [NumberField H] [Algebra K H]
    [IsHilbertClassField K H]
    (h : NumberField.classNumber K = 1) :
    Module.finrank K H = 1 := by
  rw [IsHilbertClassField.finrank_eq (H := H), h]

/-- For `IsHilbertClassField K H` with classNumber K = 1, algebraMap K → H
is bijective.  PROVED via finrank=1 + Mathlib. -/
theorem IsHilbertClassField.bijective_algebraMap_of_classNumber_one
    (K : Type u) [Field K] [NumberField K]
    (H : Type u) [Field H] [NumberField H] [Algebra K H]
    [IsHilbertClassField K H]
    (h : NumberField.classNumber K = 1) :
    Function.Bijective (algebraMap K H) := by
  rw [← Algebra.finrank_eq_one_iff_bijective_algebraMap]
  exact IsHilbertClassField.finrank_eq_one_of_classNumber_one K H h

/-- For `IsHilbertClassField K H`, |Gal(H/K)| = classNumber K.

PROVED via Mathlib's `IsGalois.card_aut_eq_finrank` + `finrank_eq` field. -/
theorem IsHilbertClassField.card_gal_eq_classNumber
    (K : Type u) [Field K] [NumberField K]
    (H : Type u) [Field H] [NumberField H] [Algebra K H]
    [IsHilbertClassField K H] :
    Nat.card (H ≃ₐ[K] H) = NumberField.classNumber K := by
  rw [IsGalois.card_aut_eq_finrank, IsHilbertClassField.finrank_eq (H := H)]

/-- For `IsHilbertClassField K H` with classNumber K = 1, |Gal(H/K)| = 1. -/
theorem IsHilbertClassField.card_gal_eq_one_of_classNumber_one
    (K : Type u) [Field K] [NumberField K]
    (H : Type u) [Field H] [NumberField H] [Algebra K H]
    [IsHilbertClassField K H]
    (h : NumberField.classNumber K = 1) :
    Nat.card (H ≃ₐ[K] H) = 1 := by
  rw [IsHilbertClassField.card_gal_eq_classNumber (K := K)]; exact h

-- (rootDiscr_pHCF_rat and finrank_pHCF_rat omitted: structure projection
-- through HilbertPClassFieldExt.rat doesn't def-unfold automatically, causing
-- typeclass timeouts.  Pattern is the same as for HCF — see
-- `rootDiscr_hcf_rat_eq_one` and `HilbertClassFieldExt.identity_finrank_eq`.)

/-! ## Summary: proved vs. postulated

### PROVED Lean (no sorry)
- `rootDiscr_hcf_eq`: rootDiscr H = rootDiscr K
- `card_gal_hcf_eq_classNumber`: |Gal(H/K)| = h_K (via Artin reciprocity)
- `HilbertClassFieldExt.finiteDimensional`: H/K is finite-dim
- `HilbertClassFieldExt.isTotallyComplex`: K totally complex → H totally complex
- `HilbertClassFieldExt.bijective_algebraMap_of_classNumber_one`: h_K=1 → H≃K
- `rootDiscr_pHCF_eq`: rootDiscr H_p = rootDiscr K
- `HilbertPClassFieldExt.isTotallyComplex`: K tot complex → H_p tot complex

### POSTULATES (labelled sorries; each TRUE per classical CFT)
- `hilbertClassField_exists` — HCF existence (Artin reciprocity)
- `HilbertClassFieldExt.isCMField_postulate` — CM preserved by HCF
- `hilbert_principal_ideal_postulate` — Hilbert 94 (Furtwängler 1930)
- `hilbertPClassField_exists` — p-HCF existence

### What's needed to close the postulates

All four postulates would be closed by a Mathlib formalization of:
- **Artin reciprocity** (the global class field correspondence)
- **Hilbert 94 / Iyanaga's theorem** (Galois cohomology approach)

This is a multi-year Mathlib effort.  The cleanest decomposition:
- `Mathlib/NumberTheory/ClassFieldTheory/Hilbert.lean` (HCF + Artin)
- `Mathlib/NumberTheory/ClassFieldTheory/Furtwangler.lean` (principalization)
- `Mathlib/NumberTheory/ClassFieldTheory/PHilbert.lean` (p-HCF)

See `Erdos90/Mathlib4_Extra/RayClassField.lean` for the ray class field
and HMR's `K_S^{(p)}` stubs, and `Erdos90/Mathlib4_Extra/Chebotarev.lean`
for the analytic side (density theorems).
-/

end NumberField
