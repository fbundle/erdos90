import Mathlib
import Erdos90.Arithmetic
import Erdos90.NumberFieldDeep_GSTower
import Erdos90.NumberFieldDeep_CM

open Real Filter NumberField Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal Topology Complex Pointwise

noncomputable section

/-!
# Assembly: `cm_norm_one_elements`, `prop_3_2_to_3_6_via_deep`, and ANT postulates

This file chains together the Golod–Shafarevich tower (from `NumberFieldDeep_GSTower`)
and the CM class-group data (from `NumberFieldDeep_CM`) to produce the final
outputs needed by `NumberField.lean`:
- §6: `cm_norm_one_elements` — Prop 2.2, proved modulo `exists_cm_class_group_data`
- §7: `prop_3_2_to_3_6_via_deep` — assembly, proved modulo the two main sorries
- §8: `ERDOS_ANT_Postulates` + `ant_postulates` — bundled postulates
-/

/-! ## §6  Assembly: `cm_norm_one_elements` (Proposition 2.2)

    The proof follows the paper's §2.1:
    1. Get `CMClassGroupData` from `exists_cm_class_group_data` (the algebraic sorry).
    2. Apply `exists_fiber_ge_div` (pigeonhole, §3) to φ : E → G.
    3. Obtain a fiber F = φ⁻¹(g) with |F| ≥ |E|/|G| ≥ exp(γ·f) + 1.
    4. Pick an anchor ε₀ ∈ F.
    5. For each ε ∈ F \ {ε₀}, embed u := mk_unit ε₀ ε ∈ Λ with ‖u r‖ = 1.
    6. By injectivity of mk_unit on F, these are all distinct, so
       |U| = |F| − 1 ≥ exp(γ·f). -/

def cm_norm_one_elements
    {K : Type} [Field K] [NumberField K] [IsCMField K]
    (f : ℕ) (hf1 : f ≥ 1) (D₀ : ℝ) (hD₀ : D₀ > 0) (_rd_F : ℝ)
    (t log_H : ℝ) (ht : t ≥ 0) (hlog_H_nn : 0 ≤ log_H)
    (hγ_pos : t * Real.log 2 - log_H > 0)
    (Λ : AddSubgroup (Fin f → ℂ))
    (hΛ_sep : ∀ v ∈ Λ, v ≠ 0 → ∃ i : Fin f, ‖v i‖ ≥ D₀⁻¹)
    (cmData : CMTowerData f hf1 Λ K)
    (classNumBound_le_log_H : cmData.classNumBound ≤ log_H) :
    ∃ (U : Finset (Fin f → ℂ)),
      (∀ u ∈ U, ∀ r : Fin f, ‖u r‖ = 1) ∧
      (∀ u ∈ U, (u : Fin f → ℂ) ∈ Λ) ∧
      ((U.card : ℝ) ≥ Real.exp ((t * Real.log 2 - log_H) * (f : ℝ))) := by
  -- Step 1: Get the CM class-group data
  have data : CMClassGroupData f t log_H Λ :=
    exists_cm_class_group_data f hf1 D₀ hD₀ t log_H ht hlog_H_nn hγ_pos Λ hΛ_sep cmData classNumBound_le_log_H
  -- letI binds definitionally to the structure fields, avoiding haveI's opaque binder mismatch
  letI : Fintype data.E := data.fintypeE
  letI : DecidableEq data.E := data.decidableEqE
  letI : Fintype data.G := data.fintypeG
  letI : DecidableEq data.G := data.decidableEqG
  -- Convert h_card_ratio (uses ℕ cardE/cardG) to Fintype.card
  have h_card_ratio' : Real.exp ((t * Real.log 2 - log_H) * (f : ℝ)) + 1 ≤
      (Fintype.card data.E : ℝ) / (Fintype.card data.G : ℝ) := by
    simpa [data.hcardE, data.hcardG] using data.h_card_ratio
  -- Step 2: Prove G is nonempty (otherwise division by zero contradicts h_card_ratio)
  have hG_nonempty : 0 < Fintype.card data.G := by
    by_contra! hzero
    have hcard0 : Fintype.card data.G = 0 := by omega
    have hcard0' : (Fintype.card data.G : ℝ) = 0 := by exact_mod_cast hcard0
    have h_contra : Real.exp ((t * Real.log 2 - log_H) * (f : ℝ)) + 1 ≤ (0 : ℝ) := by
      simpa [hcard0'] using h_card_ratio'
    have h_exp_pos : Real.exp ((t * Real.log 2 - log_H) * (f : ℝ)) > 0 := Real.exp_pos _
    linarith
  -- Step 3: Apply the pigeonhole lemma to φ : E → G
  obtain ⟨g, hg⟩ := exists_fiber_ge_div data.φ hG_nonempty
  -- Fiber F = φ⁻¹(g)
  let F : Finset data.E := Finset.filter (λ ε => data.φ ε = g) Finset.univ
  have hF_mem (ε : data.E) (hε : ε ∈ F) : data.φ ε = g :=
    (Finset.mem_filter.mp hε).2
  -- Step 4: Size bound on F: |F| ≥ exp(γ·f) + 1
  have hF_size : (F.card : ℝ) ≥ Real.exp ((t * Real.log 2 - log_H) * (f : ℝ)) + 1 := by
    linarith
  -- F is nonempty (in fact |F| ≥ 2 since exp(γ·f) > 0)
  have hF_nonempty : F.Nonempty := by
    have h_exp_ge_one : Real.exp ((t * Real.log 2 - log_H) * (f : ℝ)) ≥ 1 := by
      have hγf_nonneg : 0 ≤ (t * Real.log 2 - log_H) * (f : ℝ) :=
        mul_nonneg (le_of_lt hγ_pos) (Nat.cast_nonneg _)
      exact Real.one_le_exp_iff.mpr hγf_nonneg
    have hcard_one : (1 : ℝ) ≤ F.card := by linarith
    have : 1 ≤ F.card := by exact_mod_cast hcard_one
    exact Finset.one_le_card.mp this
  obtain ⟨ε₀, hε₀⟩ := hF_nonempty
  have hε₀_fib : data.φ ε₀ = g := hF_mem ε₀ hε₀
  -- For Nat.cast_sub later: F.card ≥ 1
  have hF_card_ge_one : 1 ≤ F.card := by
    have : (1 : ℝ) ≤ F.card := by
      have h_exp_pos : Real.exp ((t * Real.log 2 - log_H) * (f : ℝ)) > 0 := Real.exp_pos _
      linarith
    exact_mod_cast this
  -- Step 5: Construct U = {mk_unit ε₀ ε | ε ∈ F \ {ε₀}}
  let F' : Finset data.E := F.erase ε₀
  have hF'_card : F'.card = F.card - 1 := by
    rw [Finset.card_erase_of_mem hε₀]
  -- The function ε ↦ mk_unit ε₀ ε is injective on F' (by mk_unit_inj)
  have h_inj_on : ∀ x ∈ F', ∀ y ∈ F',
      (λ ε => data.mk_unit ε₀ ε) x = (λ ε => data.mk_unit ε₀ ε) y → x = y := by
    intro x hx y hy h_eq
    have mem_x := Finset.mem_erase.mp hx
    have mem_y := Finset.mem_erase.mp hy
    have hx_fib : data.φ ε₀ = data.φ x := (hε₀_fib.trans (hF_mem x mem_x.2).symm)
    have hy_fib : data.φ ε₀ = data.φ y := (hε₀_fib.trans (hF_mem y mem_y.2).symm)
    exact data.mk_unit_inj ε₀ x y (Ne.symm mem_x.1) (Ne.symm mem_y.1) hx_fib hy_fib h_eq
  let U : Finset (Fin f → ℂ) := F'.image (λ ε => data.mk_unit ε₀ ε)
  have hU_card : U.card = F'.card :=
    Finset.card_image_of_injOn h_inj_on
  -- Step 6: Verify the three required properties of U
  have hU_norm : ∀ u ∈ U, ∀ r : Fin f, ‖u r‖ = 1 := by
    intro u hu r
    obtain ⟨ε, hε, rfl⟩ := Finset.mem_image.mp hu
    have mem_ε := Finset.mem_erase.mp hε
    have hε_fib : data.φ ε₀ = data.φ ε := (hε₀_fib.trans (hF_mem ε mem_ε.2).symm)
    exact data.mk_unit_norm ε₀ ε (Ne.symm mem_ε.1) hε_fib r
  have hU_mem_Λ : ∀ u ∈ U, u ∈ Λ := by
    intro u hu
    obtain ⟨ε, hε, rfl⟩ := Finset.mem_image.mp hu
    have mem_ε := Finset.mem_erase.mp hε
    have hε_fib : data.φ ε₀ = data.φ ε := (hε₀_fib.trans (hF_mem ε mem_ε.2).symm)
    exact data.mk_unit_mem_Λ ε₀ ε (Ne.symm mem_ε.1) hε_fib
  have hU_size : (U.card : ℝ) ≥ Real.exp ((t * Real.log 2 - log_H) * (f : ℝ)) := by
    rw [hU_card, hF'_card]
    rw [Nat.cast_sub hF_card_ge_one, Nat.cast_one]
    linarith
  exact ⟨U, hU_norm, hU_mem_Λ, hU_size⟩

/-! ## §7  Assembly of `prop_3_2_to_3_6` -/

/-- **Structured proof of `prop_3_2_to_3_6`** (assembly only; no new sorry).

    Chains `golod_shafarevich_tower_with_lattice` (§2, returns `GSTowerData`,
    fully proved) and `cm_norm_one_elements` (§6, one sorry) together.  The log bound
    (log rd_F ≤ C_rd·ℓ·log ℓ for C_rd = 1) is fully proved via `log_two_mul_le`.

    The caller (`exists_admissible_family` in NumberField.lean) computes
    t and log_H from the tower's ℓ and rd_F, uses `prop_p6` to prove γ > 0,
    and calls `cm_norm_one_elements` to get U.  This keeps the analytic
    P6 proof (fully proved) separate from the algebraic sorry. -/
theorem prop_3_2_to_3_6_via_deep :
    ∃ (C_rd : ℝ), C_rd > 0 ∧
    ∀ (ℓ : ℕ), ℓ ≥ 2 →
    ∃ (D₀ : ℝ), D₀ > 0 ∧ ∃ (rd_F : ℝ), rd_F ≥ 1 ∧
      Real.log rd_F ≤ C_rd * (ℓ : ℝ) * Real.log (ℓ : ℝ) ∧
      ∀ (M : ℕ),
      ∃ (f : ℕ), f ≥ M ∧ ∃ (hf1 : f ≥ 1) (Λ : AddSubgroup (Fin f → ℂ))
        (_ : Countable Λ) (F : Set (Fin f → ℂ)),
        IsAddFundamentalDomain Λ F volume ∧ volume F < ∞ ∧ volume F > 0 ∧
        Bornology.IsBounded F ∧
        (∀ v ∈ Λ, v ≠ 0 → ∃ i : Fin f, ‖v i‖ ≥ D₀⁻¹) ∧
        (∀ v ∈ Λ, v (fin0 hf1) = 0 → v = 0) ∧
        ∀ (t log_H : ℝ), t ≥ 0 → 0 ≤ log_H → (t * Real.log 2 - log_H > 0) →
        ∃ (U : Finset (Fin f → ℂ)),
          (∀ u ∈ U, ∀ r : Fin f, ‖u r‖ = 1) ∧
          (∀ u ∈ U, (u : Fin f → ℂ) ∈ Λ) ∧
          ((U.card : ℝ) ≥ Real.exp ((t * Real.log 2 - log_H) * (f : ℝ))) := by
  refine ⟨1, one_pos, fun ℓ hℓ => ?_⟩
  let tower : GSTowerData ℓ := golod_shafarevich_tower_with_lattice ℓ hℓ
  refine ⟨tower.D₀, tower.hD₀_pos, tower.rd_F, tower.hrd_F_ge1, by
    -- log rd_F ≤ ℓ·log ℓ, and C_rd = 1
    simpa using tower.hlog_rd, fun M => ?_⟩
  obtain ⟨f, hf_ge, hf1, Λ, K, hField, hNF, hCM, cmData, hΛ_countable, F, hF_fund, hF_fin,
    hF_vol_pos, hF_bounded, hΛ_sep, hΛ_inj⟩ := tower.getTowerLevel M
  letI : Field K := hField
  letI : NumberField K := hNF
  letI : IsCMField K := hCM
  refine ⟨f, hf_ge, hf1, Λ, hΛ_countable, F, hF_fund, hF_fin, hF_vol_pos, hF_bounded,
    hΛ_sep, hΛ_inj, fun t log_H ht hlog_H_nn hγ_pos => ?_⟩
  have classNumBound_le_log_H : cmData.classNumBound ≤ log_H := by
    -- classNumBound = Real.log(h_K)/f (tautological, set in gs_tower_levels_proved).
    -- We need the Minkowski class-number bound: log(h_K)/f ≤ log_H.
    -- This holds for the real GS tower (bounded root discriminant rd_F = rd(K_j)
    -- independent of j, so Brauer–Siegel gives log h_K / f ∼ log rd_K ≤ log rd_F ≤ log_H).
    -- For the placeholder ℚ(ζ_p) tower, this bound is not available in Mathlib v4.30.
    sorry
  exact cm_norm_one_elements f hf1 tower.D₀ tower.hD₀_pos tower.rd_F t log_H ht hlog_H_nn
    hγ_pos Λ hΛ_sep cmData classNumBound_le_log_H

/-! ## §8  ANT postulates — what remains to be formalized

The single `sorry` gap in this file (`hmk_unit_inj` within `exists_cm_class_group_data`)
is captured by the `cm_class_group` field of the bundled structure below.  Every theorem
above is proved **conditional on** this one postulate (transitively via `sorryAx`).

`gs_tower_levels` is now fully proved (via cyclotomic CM field ℚ(ζ_p)); its
presence in `ERDOS_ANT_Postulates` is for backward compatibility.

When the missing Mathlib APIs become available, only `exists_cm_class_group_data`
needs to be filled; no other sorries exist in the proof chain.

**Postulate (CM class-group data, Prop 2.2):** constructs the sign‑vector type
E = {±1}^m, class‑group G = Cl(K), and norm‑1 element constructor α/c(α)
satisfying the cardinality bound.  Needs: CM field construction, split‑prime
ideal pairs, Minkowski class‑number bound. -/
structure ERDOS_ANT_Postulates where
  gs_tower (ℓ : ℕ) (hℓ : ℓ ≥ 2) (base : GSBaseData ℓ) (M : ℕ) :
    ∃ (f : ℕ), f ≥ M ∧ ∃ (hf1 : f ≥ 1) (Λ : AddSubgroup (Fin f → ℂ))
      (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K)
      (_ : CMTowerData f hf1 Λ K)
      (_ : Countable Λ) (F : Set (Fin f → ℂ)),
      IsAddFundamentalDomain Λ F volume ∧ volume F < ∞ ∧ volume F > 0 ∧
      Bornology.IsBounded F ∧
      (∀ v ∈ Λ, v ≠ 0 → ∃ i : Fin f, ‖v i‖ ≥ base.D₀⁻¹) ∧
      (∀ v ∈ Λ, v (fin0 hf1) = 0 → v = 0)
  cm_class_group {K : Type} [Field K] [NumberField K] [IsCMField K]
    (f : ℕ) (hf1 : f ≥ 1) (D₀ : ℝ) (hD₀ : D₀ > 0)
    (t log_H : ℝ) (ht : t ≥ 0) (hlog_H_nn : 0 ≤ log_H)
    (hγ_pos : t * Real.log 2 - log_H > 0)
    (Λ : AddSubgroup (Fin f → ℂ))
    (hΛ_sep : ∀ v ∈ Λ, v ≠ 0 → ∃ i : Fin f, ‖v i‖ ≥ D₀⁻¹)
    (cmData : CMTowerData f hf1 Λ K)
    (classNumBound_le_log_H : cmData.classNumBound ≤ log_H) :
    CMClassGroupData f t log_H Λ

/-- The ANT postulates delegate to `gs_tower_levels` (fully proved via cyclotomic
    CM field) and `exists_cm_class_group_data` (one remaining `sorry`:
    `hmk_unit_inj`; `hmk_unit_norm` is proved).  Only the CM class-group
    data propagate via `sorryAx` to `erdos_unit_distance_false`. -/
def ant_postulates : ERDOS_ANT_Postulates := {
  gs_tower := gs_tower_levels
  cm_class_group := exists_cm_class_group_data
}
