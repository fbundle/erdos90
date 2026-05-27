import Mathlib
import Erdos90.Arithmetic
import Erdos90.Axioms
import Erdos90.NumberFieldDeep_Analytic
import Erdos90.NumberFieldDeep_CM
import Erdos90.CMField.CyclotomicSplitPrimes
import Erdos90.CMField.QScaling
import Erdos90.CMField.QScalingLattice

open Real Filter NumberField InfinitePlace Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal Topology Complex Pointwise BigOperators

noncomputable section

/-!
# Golod–Shafarevich + Brauer–Siegel tower data — minimal axiom-based version

This file assembles the downstream Lean code
(`brd_cm_tower_postulate`, `gs_tower_levels`, `golod_shafarevich_tower_with_lattice`)
on top of the axiom `brd_tower_data` (declared in `Erdos90.Axioms`).  The
previous decomposed version of this file (`hmr_brd_cm_tower`, `gs_cm_tower`,
`chebotarev_fixed_Q`, `class_num_bound_of_brd`, their sub-postulates, etc.)
lives on the `full` branch.

On this `master` branch, the dependency closure of
`Erdos90.Main.erdos_unit_distance_false` contains exactly **one** non-Mathlib
axiom: `brd_tower_data`.  All other sorries are off-path.
-/

/-- **BRD CM tower postulate** — PROVED Lean assembly modulo `brd_tower_data`.

For each `ℓ ≥ 2`, `M ∈ ℕ`, target `(t, log_H)` with `log_H > 0`, extracts a BRD
tower level from `brd_tower_data` and assembles the full lattice data
(`Λ` = Q²-scaled Minkowski lattice, fundamental domain, separation, projection
injectivity, `CMTowerData` with `h_div_conj_mem_Λ` from Phase A,
class-number bound). -/
def brd_cm_tower_postulate (ℓ : ℕ) (hℓ : ℓ ≥ 2) (M : ℕ)
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
      cmData.classNumBound ≤ log_H := by
  set brd := brd_tower_data ℓ hℓ with hbrd_def
  obtain ⟨K, hField, hNF, hCM, hTC, f, hfM, hf1, hcompl, hreal, t', ht'_ge, sp, hspQ,
    h_classNum⟩ := brd.getTowerLevel M t log_H ht hlog_H_pos hlog_H_ge_rd
  letI : Field K := hField
  letI : NumberField K := hNF
  letI : IsCMField K := hCM
  letI : IsTotallyComplex K := hTC
  set Q := brd.Q with hQ_def
  have hQ_pos : Q > 0 := brd.hQ_pos
  let Λ : AddSubgroup (Fin f → ℂ) :=
    Erdos90.CMField.qScaledCMMinkowskiLattice K f hcompl Q hQ_pos
  let F : Set (Fin f → ℂ) :=
    Erdos90.CMField.qScaledFundamentalDomain K f hcompl Q hQ_pos
  have hCountable : Countable Λ :=
    Erdos90.CMField.qScaledCMMinkowskiLattice_countable K f hcompl Q hQ_pos
  have hFund : IsAddFundamentalDomain Λ F volume :=
    Erdos90.CMField.qScaledIsAddFundamentalDomain K f hcompl Q hQ_pos
  have hFBounded : Bornology.IsBounded F :=
    Erdos90.CMField.qScaledFundamentalDomain_bounded K f hcompl Q hQ_pos
  have hFVolLt : volume F < ∞ :=
    Erdos90.CMField.qScaledFundamentalDomain_volume_lt_top K f hcompl Q hQ_pos
  have hFVolPos : volume F > 0 :=
    Erdos90.CMField.qScaledFundamentalDomain_volume_pos K f hcompl Q hQ_pos
  have hSepRaw : ∀ v ∈ Λ, v ≠ 0 → ∃ i : Fin f, ‖v i‖ ≥ (((Q : ℝ))^2)⁻¹ :=
    Erdos90.CMField.qScaledLattice_separation K f hf1 hcompl Q hQ_pos
  have hSep : ∀ v ∈ Λ, v ≠ 0 → ∃ i : Fin f, ‖v i‖ ≥ brd.D₀⁻¹ := by
    intro v hv hv0
    obtain ⟨i, hi⟩ := hSepRaw v hv hv0
    refine ⟨i, ?_⟩
    rw [brd.hD₀_eq]
    exact hi
  have hInj : ∀ v ∈ Λ, v (fin0 hf1) = 0 → v = 0 :=
    Erdos90.CMField.qScaledLattice_first_coord_injective K f hf1 hcompl Q hQ_pos
  let φ : mixedEmbedding.mixedSpace K ≃ₗ[ℝ] (Fin f → ℂ) :=
    mixedSpace_equiv_pi_fin_of_card hreal f hcompl
  let cmData : CMTowerData f hf1 Λ K := {
    φ := φ
    h_nrComplexPlaces := hcompl
    h_nrRealPlaces := hreal
    h_φ1_norm := by
      intro r
      rw [mixedSpace_equiv_pi_fin_of_card_norm_apply hreal f hcompl (1 : K) r]
      simp
    h_φ_norm_div_conj := by
      intro α hα r
      rw [mixedSpace_equiv_pi_fin_of_card_norm_apply hreal f hcompl
        (α / IsCMField.complexConj K α) r]
      exact normAtPlace_mixedEmbedding_cm_div_conj_eq_one α hα _
    t'_param := t'
    spData := sp
    h_div_conj_mem_Λ := by
      intro ε₁ ε₂ α hα_ne hα_eq
      obtain ⟨β, hβ⟩ :=
        Erdos90.CMField.Q_sq_div_conj_mem_integers_of_spData sp ε₁ ε₂ α hα_ne hα_eq
      show (φ (NumberField.mixedEmbedding K (α / IsCMField.complexConj K α)))
        ∈ Erdos90.CMField.qScaledCMMinkowskiLattice K f hcompl Q hQ_pos
      rw [Erdos90.CMField.mem_qScaledCMMinkowskiLattice_iff K f hcompl Q hQ_pos]
      refine ⟨β, ?_⟩
      have h_cm_eq_φ :
          Erdos90.CMField.cmMinkowskiEquiv K f hcompl = φ := rfl
      rw [h_cm_eq_φ]
      have hQ_K_ne : ((Q : ℕ) : K) ≠ 0 := by
        have : Q ≠ 0 := Nat.pos_iff_ne_zero.mp hQ_pos
        exact_mod_cast this
      have hspQ_K : ((sp.Q : ℕ) : K) = ((Q : ℕ) : K) := by
        have := hspQ; exact_mod_cast this
      have h_α_eq : α / IsCMField.complexConj K α = (β : K) / (((Q : ℕ) : K)^2) := by
        rw [hβ, hspQ_K]; field_simp
      rw [h_α_eq]
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [show (φ (NumberField.mixedEmbedding K (β : K)) i) =
          (NumberField.mixedEmbedding K (β : K)).2
            ((cmComplexPlaceEquiv K f hcompl).symm i) from
        mixedSpace_equiv_pi_fin_of_card_apply hreal f hcompl _ i]
      rw [show (φ (NumberField.mixedEmbedding K ((β : K) / (((Q : ℕ) : K))^2)) i) =
          (NumberField.mixedEmbedding K ((β : K) / (((Q : ℕ) : K))^2)).2
            ((cmComplexPlaceEquiv K f hcompl).symm i) from
        mixedSpace_equiv_pi_fin_of_card_apply hreal f hcompl _ i]
      rw [mixedEmbedding.mixedEmbedding_apply_isComplex (K := K) (β : K)
          ((cmComplexPlaceEquiv K f hcompl).symm i)]
      rw [mixedEmbedding.mixedEmbedding_apply_isComplex (K := K)
          ((β : K) / (((Q : ℕ) : K))^2)
          ((cmComplexPlaceEquiv K f hcompl).symm i)]
      set w := ((cmComplexPlaceEquiv K f hcompl).symm i).val.embedding
      rw [map_div₀ w, map_pow w, map_natCast w]
      field_simp
    classNumBound := Real.log (Fintype.card (ClassGroup (𝓞 K)) : ℝ) / (f : ℝ)
    hClassNum := by
      have hf_ne : (f : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hcard_pos : (0 : ℝ) < (Fintype.card (ClassGroup (𝓞 K)) : ℝ) := by
        have h : 0 < Fintype.card (ClassGroup (𝓞 K)) :=
          Fintype.card_pos (α := ClassGroup (𝓞 K))
        exact_mod_cast h
      rw [div_mul_cancel₀ _ hf_ne, Real.exp_log hcard_pos]
  }
  refine ⟨f, hfM, hf1, Λ, K, inferInstance, inferInstance, inferInstance, cmData,
    hCountable, F, hFund, hFVolLt, hFVolPos, hFBounded, hSep, hInj, ht'_ge, ?_⟩
  show Real.log (Fintype.card (ClassGroup (𝓞 K)) : ℝ) / (f : ℝ) ≤ log_H
  exact h_classNum

/-- **Prop 3.6 + Minkowski type bridge**: tower levels with lattice.

    Takes target parameters (t, log_H) to fix the Q²-scaling and class-number bound.
    Forwards to `brd_cm_tower_postulate`. -/
def gs_tower_levels (ℓ : ℕ) (hℓ : ℓ ≥ 2) (M : ℕ)
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
  brd_cm_tower_postulate ℓ hℓ M t log_H ht hlog_H_pos hlog_H_ge_rd

/-- **Golod–Shafarevich tower data** — abstract interface for Props 3.2–3.6. -/
structure GSTowerData (ℓ : ℕ) where
  D₀ : ℝ
  hD₀_pos : D₀ > 0
  rd_F : ℝ
  hrd_F_ge1 : rd_F ≥ 1
  hlog_rd : Real.log rd_F ≤ (ℓ : ℝ) * Real.log (ℓ : ℝ)
  getTowerLevel (M : ℕ) (t log_H : ℝ) (ht : t ≥ 0) (hlog_H_pos : log_H > 0)
      (hlog_H_ge_rd : log_H ≥ 2 * Real.log (2 * rd_F)) :
    ∃ (f : ℕ), f ≥ M ∧ ∃ (hf1 : f ≥ 1)
    (Λ : AddSubgroup (Fin f → ℂ))
    (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K)
    (cmData : CMTowerData f hf1 Λ K)
    (_ : Countable Λ) (F : Set (Fin f → ℂ)),
    IsAddFundamentalDomain Λ F volume ∧ volume F < ∞ ∧ volume F > 0 ∧
    Bornology.IsBounded F ∧
    (∀ v ∈ Λ, v ≠ 0 → ∃ i : Fin f, ‖v i‖ ≥ D₀⁻¹) ∧
    (∀ v ∈ Λ, v (fin0 hf1) = 0 → v = 0) ∧
    t + 1 ≤ (cmData.t'_param : ℝ) ∧
    cmData.classNumBound ≤ log_H

/-- **Golod–Shafarevich tower with lattice** (Props 3.2–3.6).

    Assembly of `brd_tower_data` (axiom) and `gs_tower_levels` (proved). -/
def golod_shafarevich_tower_with_lattice (ℓ : ℕ) (hℓ : ℓ ≥ 2) : GSTowerData ℓ :=
  let brd := brd_tower_data ℓ hℓ
  { D₀ := brd.D₀
    hD₀_pos := brd.hD₀_pos
    rd_F := brd.rd_F
    hrd_F_ge1 := brd.hrd_F_ge1
    hlog_rd := brd.hlog_rd
    getTowerLevel := fun M t log_H ht hlog_H_pos hlog_H_ge_rd =>
      gs_tower_levels ℓ hℓ M t log_H ht hlog_H_pos hlog_H_ge_rd }
