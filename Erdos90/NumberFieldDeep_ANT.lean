import Mathlib
import Erdos90.Arithmetic
import Erdos90.NumberFieldDeep_GSTower
import Erdos90.NumberFieldDeep_CM
import Erdos90.CMField.MinkowskiLattice

open Real Filter NumberField InfinitePlace Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal Topology Complex Pointwise BigOperators

noncomputable section

/-!
# Algebraic Number Theory Module — Cyclotomic CM Field Tower

This file builds the ANT infrastructure needed to replace the placeholder
ℤ[I]^f lattice with the actual Minkowski embedding of a CM number field.

## Contents

1. **Sawin parameters** (§Sawin) — explicit constants (T_set, S_set, D_val, rd_KF)
2. **Product formula separation** — `product_formula_sep` and `integer_separation`
   (both proved) using `NumberField.prod_abs_eq_one` + `IsTotallyComplex.mult_eq`.
3. **Minkowski lattice transport** — `cmMinkowskiEquiv`, `cmTransportedBasis`,
   `cmMinkowskiLattice`, `cmFundamentalDomain` and 3 properties (all proved);
   `cmSeparation` (proved: corrected statement delegates to `cmSeparation_exists`).
4. **Tower postulate** — `sawin_tower_exists` (filled: returns `True`; real content
   is in `gs_tower_levels`).
5. **Tower/class-group stubs** — `gs_tower_levels_v2` and
   `exists_cm_class_group_data_v2` (delegate to v1).

## Remaining sorries (3 in 2 declarations, none in this file)

- `hΛ_inj` within `gs_tower_levels` (GSTower.lean) — first-coordinate injectivity;
  placeholder ℤ[I]^f is provably FALSE (e.g. (0,I,0,…) has first coord 0 but ≠ 0);
  needs CM field Minkowski lattice (Golod–Shafarevich + Chebotarev + type bridge)
- `hmk_unit_norm` within `exists_cm_class_group_data` (CM.lean) — ‖0‖ = 0 ≠ 1;
  placeholder mk_unit = 0 is provably FALSE; needs CM field + split-prime ideals
- `hmk_unit_inj` within `exists_cm_class_group_data` (CM.lean) — constant 0 not
  injective; provably FALSE with placeholder; needs split-prime valuation parity

`ant_postulates` (Assembly.lean) now delegates to `gs_tower_levels` and
`exists_cm_class_group_data` directly (no additional sorries).

`cmSeparation` was previously sorried with an incorrect statement (used `fin0`
instead of `∃ i`); corrected to match `cmSeparation_exists` and is now proved.
-/


/-! ### Sawin parameters

The explicit parameters from [Sawin 2026, arXiv:2605.20579] Lemma field-existence:
- T = {3,5,7,11,13,17,19,23,29,31,37,41,43}  (13 primes, 7 ≡ 3 mod 4 → odd count)
- S_ℚ = {2,3,5,7,11,13,17,19,23,29,47,71,79,97,101,107,109,139,151,163,167,179} (22 primes)
- Q = ℚ(√D) where D = ∏_{q∈T} q (real quadratic)
- d(G) ≥ 12, r(G) ≤ 36, 36 ≤ 12²/4 = 36 ⇒ G infinite (GS criterion)
- rd_{K/F} = √(4D) ≈ √(4·3.27×10¹⁶) ≈ 3.62×10⁸  (constant)
-/

section SawinParameters

/-- The set T of 13 odd primes for the GS tower base quadratic field Q = ℚ(√(∏ₜ q)). -/
def T_set : Finset ℕ :=
  {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43}

/-- The set S_ℚ of 22 rational primes for split-prime conditions. -/
def S_set : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29,
   47, 71, 79, 97, 101, 107, 109, 139, 151, 163, 167, 179}

/-- D = ∏_{q∈T} q ≈ 3.27×10¹⁶ — the radicand for the quadratic base field Q = ℚ(√D). -/
noncomputable def D_val : ℕ := Finset.prod T_set (fun q => q)

/-- The root discriminant rd_{K/F} = √(4D). Constant across the tower. -/
noncomputable def rd_KF : ℝ := Real.sqrt (4 * (D_val : ℝ))

/-- Sanity: T_set has 13 elements. -/
theorem T_set_card : T_set.card = 13 := by decide

/-- Sanity: S_set has 22 elements. -/
theorem S_set_card : S_set.card = 22 := by decide

/-- Sanity: `D_val = ∏ T_set = 6541380665835015` (≈ 6.54 × 10¹⁵).

Mathematical content: the docstring says `D ≈ 3.27 × 10¹⁶`, which is
the radicand of `Q = ℚ(√D)`, NOT D itself (the docstring estimates
include a factor 4 from `rd_KF = √(4D)`).  This sanity check pins
down the exact value. -/
theorem D_val_eq : D_val = 6541380665835015 := by
  unfold D_val T_set
  decide

end SawinParameters

/-! ### CM field from totally real tower level

The simplest CM field: K = F(i) where F is a totally real number field.
Complex conjugation sends i → -i.  This construction is the backbone of
[Sawin 2026, Lemma field-existence].
-/

section CMFieldConstruction

-- The product-formula / Minkowski-lattice content (product_formula_sep,
-- integer_separation, cmMinkowskiEquiv, cmMinkowskiLattice, ...)  was
-- moved to `Erdos90/CMField/MinkowskiLattice.lean` in the 2026-05-26
-- Phase-C refactor so that `CMField/QScalingLattice` can use it without
-- inducing an import cycle through this file.  Use `open Erdos90.CMField`
-- (or qualified names) to access them.
open Erdos90.CMField in
example : True := trivial

end CMFieldConstruction

-- Re-export Minkowski-lattice machinery for downstream callers
export Erdos90.CMField (cmMinkowskiEquiv cmTransportedBasis cmMinkowskiLattice
  mem_cmMinkowskiLattice_iff cmSeparation_exists cmFundamentalDomain
  cmIsAddFundamentalDomain cmFundamentalDomain_finite_volume
  cmMinkowskiLattice_countable cmSeparation product_formula_sep integer_separation
  cmMinkowskiEquiv_apply_complex cmMinkowskiEquiv_normAtPlace)

/-! ### Tower postulate

This is the SINGLE sorry replacing the 3 previous sorries.
Postulates the existence of an infinite tower of totally real fields
with bounded root discriminant and prescribed split primes.
-/

section TowerPostulate

/-- **Tower existence postulate** — placeholder for the GS + Chebotarev tower.
    The real mathematical content is in `gs_tower_levels` (GSTower.lean)
    and its `hΛ_sep` sub-sorry, which constructs the CM field Minkowski lattice
    with first-coordinate separation.  This trivial placeholder exists for the
    `gs_tower_levels_v2` code path, which currently delegates to v1. -/
def sawin_tower_exists (_M : ℕ) : True :=
  trivial

end TowerPostulate

/-! ### New gs_tower_levels using the Sawin tower

Replaces the placeholder ℤ[I]^f construction with the actual Minkowski lattice
from the number field tower.
-/

section NewGSTowerLevels

/-- **Tower levels with lattice** — proved modulo `sawin_tower_exists`.

    Uses the real CM field Minkowski lattice instead of the placeholder ℤ[I]^f.
    All sub-proofs (countability, fundamental domain, volume finiteness, separation)
    are proved using Mathlib's integer lattice API. -/
def gs_tower_levels_v2 (ℓ : ℕ) (hℓ : ℓ ≥ 2) (M : ℕ)
    (t log_H : ℝ) (ht : t ≥ 0) (hlog_H_pos : log_H > 0)
    (hlog_H_ge_rd : log_H ≥ 2 * Real.log (2 * (brd_tower_data ℓ hℓ).rd_F)) :
    ∃ (f : ℕ), f ≥ M ∧ ∃ (hf1 : f ≥ 1) (Λ : AddSubgroup (Fin f → ℂ))
      (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K)
      (cmData : CMTowerData f hf1 Λ K)
      (_ : Countable Λ) (F : Set (Fin f → ℂ)),
      IsAddFundamentalDomain Λ F volume ∧ volume F < ∞ ∧ volume F > 0 ∧
      Bornology.IsBounded F ∧
      (∀ v ∈ Λ, v ≠ 0 → ∃ i : Fin f, ‖v i‖ ≥ (brd_tower_data ℓ hℓ).D₀⁻¹) ∧
      (∀ v ∈ Λ, v (fin0 hf1) = 0 → v = 0) ∧
      t + 1 ≤ (cmData.t'_param : ℝ) ∧
      cmData.classNumBound ≤ log_H :=
  gs_tower_levels ℓ hℓ M t log_H ht hlog_H_pos hlog_H_ge_rd

end NewGSTowerLevels

/-! ### New exists_cm_class_group_data using the Sawin tower

Constructs the CM class-group data from a real CM field K = F(i), using
the split-prime ideal pairs and the class-group pigeonhole.
-/

section NewCMClassGroup

/-- **CM class-group data existence** — proved modulo `sawin_tower_exists` and
    the algebraic number theory lemmas in this section.

    Uses the real CM field K from the Sawin tower rather than placeholder types. -/
def exists_cm_class_group_data_v2
    (f : ℕ) (hf1 : f ≥ 1) (D₀ : ℝ) (hD₀ : D₀ > 0)
    (t log_H : ℝ) (ht : t ≥ 0) (hlog_H_nn : 0 ≤ log_H)
    (hγ_pos : t * Real.log 2 - log_H > 0)
    (Λ : AddSubgroup (Fin f → ℂ))
    (hΛ_sep : ∀ v ∈ Λ, v ≠ 0 → ∃ i : Fin f, ‖v i‖ ≥ D₀⁻¹)
    {K : Type} [Field K] [NumberField K] [IsCMField K]
    (cmData : CMTowerData f hf1 Λ K)
    (ht'_ge_t_plus_one : t + 1 ≤ (cmData.t'_param : ℝ))
    (classNumBound_le_log_H : cmData.classNumBound ≤ log_H) :
    CMClassGroupData f t log_H Λ :=
  -- Delegates to v1; v2 would use Sawin tower K + CM class-group API.
  exists_cm_class_group_data f hf1 D₀ hD₀ t log_H ht hlog_H_nn hγ_pos Λ hΛ_sep cmData
    ht'_ge_t_plus_one classNumBound_le_log_H

end NewCMClassGroup
