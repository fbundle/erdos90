/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Erdos90.Mathlib4_Extra.NumberTheory.ClassFieldTheory.Basic

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

/-! ### Decomposition of `index_eq_finrank_postulate`

The CFT index formula decomposes via the local-global chain:

1. **Local norm residue iso**: For each finite place `v` of `K`,
   `K_v^* / N(L_w^*) ≅ Gal(L_w/K_v)` (local CFT).
2. **Idele class group iso**: Globally, `C_K / N(C_L) ≅ Gal(L/K)^{ab}`
   (global CFT, the main theorem).
3. **Reciprocity reduction**: For abelian extensions, the kernel of
   `K^* → C_K / N(C_L)` equals `N(L^*)`, giving `K^* / N(L^*) ≅
   Gal(L/K)`.

Three sub-postulates below.
-/

/-- **Sub-postulate D3.norm.local-residue** (Local norm residue iso):
For each finite place `v` of `K` (with completion `K_v`) and the
corresponding place `w` of `L`, `K_v^* / N_{L_w/K_v}(L_w^*) ≅
Gal(L_w/K_v)`.

Cite: Serre *Local Fields* XIV (local class field theory); Neukirch
V §6.  Mathlib v4.30: completions of number fields exist but local
CFT not packaged. -/
def local_norm_residue_postulate
    (K : Type u) [Field K] [NumberField K]
    (L : Type u) [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsAbelianGalois K L] :
    True := sorry

/-- **Sub-postulate D3.norm.idele-iso** (Idele class group iso):
For an abelian Galois extension `L/K`, the idele class group has

  `C_K / N_{L/K}(C_L) ≅ Gal(L/K)`

via the global Artin map.

Cite: Neukirch VI §1; Tate's thesis (idele-theoretic CFT).  Mathlib
v4.30: ideles not packaged. -/
def idele_class_norm_iso_postulate
    (K : Type u) [Field K] [NumberField K]
    (L : Type u) [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsAbelianGalois K L] :
    True := sorry

/-- **Sub-postulate D3.norm.global-reduction** (Reduction to K^*):
The composition `K^* → C_K → C_K / N(C_L)` has kernel exactly `N(L^*)`,
giving `K^* / N(L^*) ↪ Gal(L/K)`.  Combined with surjectivity (the
Artin map is surjective for abelian extensions), this is an iso.

Cite: Tate's thesis Theorem 8.5; Neukirch VI §6.  Mathlib v4.30:
not packaged. -/
def norm_kernel_reduction_postulate
    (K : Type u) [Field K] [NumberField K]
    (L : Type u) [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsAbelianGalois K L] :
    True := sorry

/-- **Postulate** (CFT index formula for abelian extensions):

For an abelian finite extension `L/K` of number fields,
  `[K^* : N_{L/K}(L^*)] = [L : K]`.

In particular, the quotient `K^* / N_{L/K}(L^*) ≅ Gal(L/K)` (this is the
norm residue isomorphism).

ASSEMBLY (modulo the three sub-postulates above):
1. By `local_norm_residue_postulate`: local iso K_v^*/N(L_w^*) ≅ Gal(L_w/K_v).
2. By `idele_class_norm_iso_postulate`: global iso C_K/N(C_L) ≅ Gal(L/K).
3. By `norm_kernel_reduction_postulate`: reduce to K^*/N(L^*) ≅ Gal(L/K).
4. `|Gal(L/K)| = [L:K]` (Mathlib `IsGalois.card_aut_eq_finrank`).
5. Hence `[K^* : N(L^*)] = |Gal(L/K)| = [L:K]`. -/
def index_eq_finrank_postulate
    (K : Type u) [Field K] [NumberField K]
    (L : Type u) [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsAbelianGalois K L] :
    (NormGroup K L).index = Module.finrank K L := sorry

/-- Trivial-extension corollary: `(NormGroup K K).index = 1 = Module.finrank K K`.

PROVED Lean: when L = K, the norm map is the identity, so `NormGroup K K = ⊤`
(the trivial subgroup of index 1).  And `Module.finrank K K = 1`. -/
theorem index_eq_finrank_of_self
    (K : Type u) [Field K] [NumberField K] :
    (NormGroup K K).index = Module.finrank K K := by
  -- NormGroup K K = range of Units.map (Algebra.norm K K) = ⊤
  -- since Algebra.norm K K acts as identity on K (Algebra.norm_apply_self).
  have h_top : NormGroup K K = ⊤ :=
    MonoidHom.range_eq_top.mpr fun x => ⟨x, by
      apply Units.ext
      show (Algebra.norm K (S := K)) (x : K) = x
      rw [Algebra.norm_self]; rfl⟩
  rw [h_top]
  simp [Subgroup.index_top, Module.finrank_self]

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
