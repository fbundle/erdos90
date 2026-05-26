import Mathlib
import Erdos90.NumberFieldDeep_CM

open Real Filter NumberField InfinitePlace Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal Topology Complex Pointwise BigOperators

namespace Erdos90.CMField

noncomputable section

/-!
# Unscaled CM Minkowski lattice (no Q-scaling)

The unscaled Minkowski lattice `Λ = Φ(𝓞_K) ⊂ ℂ^f` of a totally complex CM
field `K`, with fundamental domain, separation (`‖v_i‖ ≥ 1` for nonzero
lattice points via the product formula), and countability.

This file was previously the `MinkowskiLatticeFromCMField` section of
`Erdos90/NumberFieldDeep_ANT.lean`, but it is needed by both
`Erdos90/CMField/QScalingLattice.lean` (the Q²-scaled version, built by
mapping the unscaled lattice via `v ↦ Q⁻² • v`) and the original
`NumberFieldDeep_ANT.lean` itself.  Promoting it into its own file in
`CMField/` lets `QScalingLattice` and `GSTower` import it without
inducing a cycle through `ANT`.
-/

section CMFieldConstruction

variable {K : Type*} [Field K] [NumberField K]

end CMFieldConstruction

section ProductFormula

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

/-- Product formula separation: for a nonzero algebraic integer β in a totally complex
    number field K, the product of all archimedean absolute values (without multiplicity) is ≥ 1.
    For totally complex fields, `mult w = 2` for every infinite place, so
    `∏ w β = sqrt(|N(β)|)` and `|N(β)| ≥ 1` gives the result.
    Requires `[IsTotallyComplex K]` because the argument fails for fields with real places. -/
lemma product_formula_sep
    (a : 𝓞 K) (ha0 : a ≠ 0) :
    (∏ w : InfinitePlace K, mixedEmbedding.normAtPlace w (NumberField.mixedEmbedding K (a : K))) ≥ 1 := by
  simp_rw [mixedEmbedding.normAtPlace_apply]
  have ha0' : (a : K) ≠ 0 := by
    intro h; apply ha0; exact Subtype.ext h
  have hpform := NumberField.prod_abs_eq_one ha0'
  have hfin : ∏ᶠ w : FinitePlace K, w a = (|Algebra.norm ℤ a| : ℝ)⁻¹ := by
    simpa using NumberField.FinitePlace.prod_eq_inv_abs_norm_int ha0
  have hfin_coe : ∏ᶠ w : FinitePlace K, w (a : K) = ∏ᶠ w : FinitePlace K, w a := by simp
  rw [hfin_coe, hfin] at hpform
  have hN_ge_one : (1 : ℝ) ≤ (|Algebra.norm ℤ a| : ℝ) := by
    have h := Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr ha0)
    exact_mod_cast h
  have hN_ne_zero : (|Algebra.norm ℤ a| : ℝ) ≠ 0 := by linarith
  have hP_eq_N : (∏ w : InfinitePlace K, w (a : K) ^ w.mult) = (|Algebra.norm ℤ a| : ℝ) := by
    calc
      (∏ w : InfinitePlace K, w (a : K) ^ w.mult) =
          ((∏ w : InfinitePlace K, w (a : K) ^ w.mult) * (|Algebra.norm ℤ a| : ℝ)⁻¹) *
            (|Algebra.norm ℤ a| : ℝ) := by
        field_simp [hN_ne_zero]
      _ = 1 * (|Algebra.norm ℤ a| : ℝ) := by rw [hpform]
      _ = (|Algebra.norm ℤ a| : ℝ) := by simp
  have h_mult_two : ∀ w : InfinitePlace K, w.mult = 2 := fun w => IsTotallyComplex.mult_eq w
  simp_rw [h_mult_two] at hP_eq_N
  have h_sq_eq : (∏ w : InfinitePlace K, (w (a : K)) ^ 2) =
      ((∏ w : InfinitePlace K, w (a : K)) ^ 2) := by
    simp [Finset.prod_pow]
  rw [h_sq_eq] at hP_eq_N
  have h_prod_nonneg : 0 ≤ ∏ w : InfinitePlace K, w (a : K) :=
    Finset.prod_nonneg (fun w _ => apply_nonneg _ _)
  nlinarith

/-- For a nonzero integer a ≠ 0 in a totally complex K, there exists an infinite place w
    with |mixedEmbedding.normAtPlace w (mixedEmbedding K (a : K))| ≥ 1. -/
lemma integer_separation
    (a : 𝓞 K) (ha0 : a ≠ 0) :
    ∃ w : InfinitePlace K,
      mixedEmbedding.normAtPlace w (NumberField.mixedEmbedding K (a : K)) ≥ 1 := by
  set f := fun (w : InfinitePlace K) =>
    mixedEmbedding.normAtPlace w (NumberField.mixedEmbedding K (a : K)) with hf
  have hprod : (∏ w : InfinitePlace K, f w) ≥ 1 := product_formula_sep K a ha0
  have h_nonneg : ∀ w, 0 ≤ f w := fun w => mixedEmbedding.normAtPlace_nonneg w _
  haveI : Nonempty (InfinitePlace K) := by
    have h_card_pos : 0 < Fintype.card (InfinitePlace K) := by
      have h_no_real : nrRealPlaces K = 0 := IsTotallyComplex.nrRealPlaces_eq_zero K
      rw [card_eq_nrRealPlaces_add_nrComplexPlaces (K := K), h_no_real, zero_add]
      have h_rank := card_add_two_mul_card_eq_rank (K := K)
      rw [h_no_real] at h_rank
      by_contra! hzero
      have hzero' : nrComplexPlaces K = 0 := by omega
      rw [hzero'] at h_rank
      have h_finrank_pos : 0 < Module.finrank ℚ K :=
        Module.finrank_pos (R := ℚ) (M := K)
      omega
    exact Fintype.card_pos_iff.mp h_card_pos
  by_contra! h_all
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  have h_prod_lt_one : (∏ w : InfinitePlace K, f w) < 1 := by
    classical
      have hw₀_mem : w₀ ∈ (Finset.univ : Finset (InfinitePlace K)) := Finset.mem_univ _
      calc
        (∏ w : InfinitePlace K, f w) =
            (∏ w ∈ (Finset.univ : Finset (InfinitePlace K)), f w) := by simp
        _ = f w₀ * (∏ w ∈ (Finset.univ : Finset (InfinitePlace K)).erase w₀, f w) := by
          rw [← Finset.prod_erase_mul (Finset.univ : Finset (InfinitePlace K)) f hw₀_mem,
              mul_comm]
        _ ≤ f w₀ * (∏ _w ∈ (Finset.univ : Finset (InfinitePlace K)).erase w₀, (1 : ℝ)) := by
          refine mul_le_mul_of_nonneg_left
            (Finset.prod_le_prod (fun w _ => h_nonneg w)
              (fun w hw => (h_all w).le)) (h_nonneg w₀)
        _ = f w₀ := by simp
        _ < 1 := h_all w₀
  linarith

end ProductFormula

section MinkowskiLatticeFromCMField

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

/-- The linear equivalence φ : mixedSpace K ≃ₗ[ℝ] (Fin f → ℂ) obtained by composing
    `mixedSpace_equiv_complex_places` with a `Fin` index equivalence. -/
def cmMinkowskiEquiv (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f) :
    mixedEmbedding.mixedSpace K ≃ₗ[ℝ] (Fin f → ℂ) :=
  mixedSpace_equiv_pi_fin_of_card (IsTotallyComplex.nrRealPlaces_eq_zero K) f hf

/-- Applying `cmMinkowskiEquiv` at index `cmComplexPlaceEquiv K f hf w` returns
    the second component of the mixed-space element at `w`. -/
lemma cmMinkowskiEquiv_apply_complex (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f)
    (x : mixedEmbedding.mixedSpace K) (w : {w : InfinitePlace K // InfinitePlace.IsComplex w}) :
    cmMinkowskiEquiv K f hf x ((cmComplexPlaceEquiv K f hf) w) = x.2 w := by
  dsimp [cmMinkowskiEquiv, cmComplexPlaceEquiv, mixedSpace_equiv_pi_fin_of_card,
    mixedSpace_equiv_complex_places, prod_left_isEmpty_equiv_snd]
  simp

/-- The norm of `cmMinkowskiEquiv` at coordinate `cmComplexPlaceEquiv K f hf w`
    equals `mixedEmbedding.normAtPlace w`. -/
lemma cmMinkowskiEquiv_normAtPlace (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f)
    (a : 𝓞 K) (w : {w : InfinitePlace K // InfinitePlace.IsComplex w}) :
    ‖cmMinkowskiEquiv K f hf (NumberField.mixedEmbedding K (a : K))
      ((cmComplexPlaceEquiv K f hf) w)‖ =
    mixedEmbedding.normAtPlace (w : InfinitePlace K) (NumberField.mixedEmbedding K (a : K)) := by
  rw [cmMinkowskiEquiv_apply_complex]
  rw [mixedEmbedding.normAtPlace_apply_of_isComplex w.prop]

/-- Transported basis: `mixedEmbedding.latticeBasis K` mapped through `cmMinkowskiEquiv`. -/
def cmTransportedBasis (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f) :
    Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) ℝ (Fin f → ℂ) :=
  (mixedEmbedding.latticeBasis K).map (cmMinkowskiEquiv K f hf)

/-- The CM Minkowski lattice: ℤ-span of the transported basis. -/
def cmMinkowskiLattice (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f) :
    AddSubgroup (Fin f → ℂ) :=
  (Submodule.span ℤ (Set.range (cmTransportedBasis K f hf))).toAddSubgroup

lemma mem_cmMinkowskiLattice_iff (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f)
    (x : Fin f → ℂ) :
    x ∈ cmMinkowskiLattice K f hf ↔
      ∃ a : 𝓞 K, cmMinkowskiEquiv K f hf (NumberField.mixedEmbedding K (a : K)) = x := by
  have h_span_eq_map : (Submodule.span ℤ (Set.range (cmTransportedBasis K f hf))) =
      Submodule.map
        ((cmMinkowskiEquiv K f hf).toLinearMap.restrictScalars ℤ)
        (mixedEmbedding.integerLattice K) := by
    calc
      Submodule.span ℤ (Set.range (cmTransportedBasis K f hf)) =
          Submodule.span ℤ (Set.range ((mixedEmbedding.latticeBasis K).map
            (cmMinkowskiEquiv K f hf))) := rfl
      _ = Submodule.span ℤ ((cmMinkowskiEquiv K f hf) ''
          Set.range (mixedEmbedding.latticeBasis K)) := by
        have h_range_eq : Set.range ((mixedEmbedding.latticeBasis K).map
            (cmMinkowskiEquiv K f hf)) =
            (cmMinkowskiEquiv K f hf) ''
              Set.range (mixedEmbedding.latticeBasis K) := by
          ext z; simp
        rw [h_range_eq]
      _ = Submodule.map ((cmMinkowskiEquiv K f hf).toLinearMap.restrictScalars ℤ)
          (Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis K))) := by
        simp [Submodule.map_span]
      _ = Submodule.map ((cmMinkowskiEquiv K f hf).toLinearMap.restrictScalars ℤ)
          (mixedEmbedding.integerLattice K) := by
        rw [mixedEmbedding.span_latticeBasis K]
  dsimp [cmMinkowskiLattice]
  rw [h_span_eq_map]
  constructor
  · intro hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy_int, hy_eq⟩
    rcases LinearMap.mem_range.mp hy_int with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [← hy_eq]
    have ha_simp : ((mixedEmbedding K).comp (algebraMap (𝓞 K) K)).toIntAlgHom.toLinearMap a =
        NumberField.mixedEmbedding K (a : K) := by simp
    simpa [ha_simp] using ha
  · intro ⟨a, ha⟩
    rw [← ha]
    apply Submodule.mem_map.mpr
    have h_mem : NumberField.mixedEmbedding K (a : K) ∈
        mixedEmbedding.integerLattice K := by
      apply LinearMap.mem_range.mpr
      refine ⟨a, ?_⟩
      simp
    exact ⟨NumberField.mixedEmbedding K (a : K), h_mem, rfl⟩

/-- Separation: for nonzero `v` in the CM Minkowski lattice and `D₀ ≥ 1`,
some coordinate has `‖v i‖ ≥ D₀⁻¹`. -/
lemma cmSeparation_exists (f : ℕ) (_hf1 : f ≥ 1) (hf : InfinitePlace.nrComplexPlaces K = f)
    (D₀ : ℝ) (hD₀ : D₀ > 0) (hD₀_ge_one : D₀ ≥ 1) :
    ∀ v ∈ cmMinkowskiLattice K f hf, v ≠ 0 →
      ∃ i : Fin f, ‖v i‖ ≥ D₀⁻¹ := by
  intro v hv hv0
  have hD₀_inv_le_one : D₀⁻¹ ≤ 1 := by
    simpa [one_div] using
      (one_div_le_one_div hD₀ (by norm_num : (0 : ℝ) < 1)).mpr hD₀_ge_one
  rcases (mem_cmMinkowskiLattice_iff K f hf v).mp hv with ⟨a, ha⟩
  have ha0 : a ≠ 0 := by
    intro hzero
    apply hv0
    have hzero' : (a : K) = 0 := by exact_mod_cast hzero
    rw [hzero', map_zero, map_zero] at ha
    exact ha.symm
  obtain ⟨w, hw⟩ := integer_separation K a ha0
  have hw_complex : InfinitePlace.IsComplex w := IsTotallyComplex.isComplex w
  let w' : {w : InfinitePlace K // InfinitePlace.IsComplex w} := ⟨w, hw_complex⟩
  let idx : Fin f := cmComplexPlaceEquiv K f hf w'
  have hnorm : ‖v idx‖ ≥ 1 := by
    rw [← ha]
    rw [cmMinkowskiEquiv_normAtPlace K f hf a w']
    exact hw
  refine ⟨idx, le_trans hD₀_inv_le_one hnorm⟩

/-- Fundamental domain for the CM Minkowski lattice. -/
noncomputable def cmFundamentalDomain (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f) :
    Set (Fin f → ℂ) :=
  ZSpan.fundamentalDomain (cmTransportedBasis K f hf)

lemma cmIsAddFundamentalDomain (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f) :
    IsAddFundamentalDomain (cmMinkowskiLattice K f hf)
      (cmFundamentalDomain K f hf) volume := by
  dsimp [cmMinkowskiLattice, cmFundamentalDomain]
  exact ZSpan.isAddFundamentalDomain' (cmTransportedBasis K f hf) volume

lemma cmFundamentalDomain_finite_volume (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f) :
    volume (cmFundamentalDomain K f hf) < ∞ := by
  dsimp [cmFundamentalDomain]
  have h_bounded : Bornology.IsBounded (ZSpan.fundamentalDomain (cmTransportedBasis K f hf)) :=
    ZSpan.fundamentalDomain_isBounded _
  rcases h_bounded.subset_closedBall (0 : Fin f → ℂ) with ⟨R, hR⟩
  apply lt_of_le_of_lt (measure_mono hR)
  haveI : FiniteDimensional ℝ (Fin f → ℂ) := inferInstance
  haveI : ProperSpace (Fin f → ℂ) := FiniteDimensional.proper ℝ (Fin f → ℂ)
  exact measure_closedBall_lt_top

lemma cmMinkowskiLattice_countable (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f) :
    Countable (cmMinkowskiLattice K f hf) := by
  dsimp [cmMinkowskiLattice]
  change Countable (Submodule.span ℤ (Set.range (cmTransportedBasis K f hf)))
  infer_instance

lemma cmSeparation (f : ℕ) (hf1 : f ≥ 1) (hf : InfinitePlace.nrComplexPlaces K = f)
    (D₀ : ℝ) (hD₀ : D₀ > 0) (hD₀_ge_one : D₀ ≥ 1) :
    ∀ v ∈ cmMinkowskiLattice K f hf, v ≠ 0 →
      ∃ i : Fin f, ‖v i‖ ≥ D₀⁻¹ :=
  cmSeparation_exists K f hf1 hf D₀ hD₀ hD₀_ge_one

end MinkowskiLatticeFromCMField

end

end Erdos90.CMField
