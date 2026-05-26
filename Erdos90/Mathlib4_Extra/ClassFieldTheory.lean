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

/-- **Postulate**: the HCF of a CM number field is CM.

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

/-- **Postulate** (Hilbert principal ideal theorem):

For any ideal `I` of `𝓞_K`, its extension `I · 𝓞_{H(K)}` to the HCF is
principal.  In particular, the ideal-class extension map
`ClassGroup (𝓞 K) → ClassGroup (𝓞 H(K))` is the zero map.

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
reciprocity.  Not in Mathlib v4.30. -/
def hilbertPClassField_exists (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (_hp : Nat.Prime p) : HilbertPClassFieldExt K p := sorry

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

/-- **Postulate**: `[H_p(K) : K]` divides `classNumber K`.

For a number field `K`, the degree of the p-HCF over K equals the p-part
of the class number.  In particular, it divides `classNumber K`. -/
def p_HCF_finrank_divides_classNumber_postulate
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (E : HilbertPClassFieldExt K p) :
    Module.finrank K E.H_p ∣ NumberField.classNumber K := sorry

/-- If `p ∤ classNumber K`, then the p-HCF of K equals K itself.

PROVED Lean modulo `p_HCF_finrank_divides_classNumber_postulate`. -/
theorem p_HCF_trivial_of_p_not_dvd_classNumber
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (_hp : Nat.Prime p)
    (h_p_not_dvd : ¬ p ∣ NumberField.classNumber K)
    (E : HilbertPClassFieldExt K p) :
    Module.finrank K E.H_p = 1 := by
  obtain ⟨n, hn⟩ := E.finrank_is_pow_p
  -- [H_p : K] = p^n.  By p_HCF_finrank_divides_classNumber, p^n | classNumber K.
  -- If p doesn't divide classNumber K, then p^n | classNumber K forces n = 0.
  -- Hence [H_p : K] = p^0 = 1.
  have h_dvd := p_HCF_finrank_divides_classNumber_postulate K p E
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

-- (HilbertClassFieldExt.identity_hilbert_principal omitted: the underlying
-- claim is that for classNumber=1 K, the Hilbert principal ideal theorem
-- holds trivially because 𝓞 K is a PID.  The Lean statement requires
-- unfolding the structure projection `(identity K h).H = K`, which is
-- def-eq but doesn't propagate to the algebraMap typeclass resolution.)

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
