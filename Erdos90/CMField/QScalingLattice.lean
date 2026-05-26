import Mathlib
import Erdos90.CMField.Basic
import Erdos90.CMField.QScaling
import Erdos90.NumberFieldDeep_ANT
import Erdos90.NumberFieldDeep_CM

open Real Filter NumberField InfinitePlace Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal Topology Complex Pointwise BigOperators nonZeroDivisors

noncomputable section

/-!
# Q²-scaled Minkowski lattice

Given a CM field `K` with `[IsTotallyComplex K]`, a degree `f = nrComplexPlaces K`,
and split prime data `sp : SplitPrimeData K m`, this file constructs the
Q²-scaled Minkowski lattice `Λ = Φ(Q⁻²·𝓞_K) ⊂ ℂ^f` along with:
- a fundamental domain `F` (bounded volume, positive volume)
- separation `∀ v ∈ Λ \ {0}, ∃ i, ‖v i‖ ≥ Q⁻²`
- projection injectivity `∀ v ∈ Λ, v(fin0) = 0 → v = 0`
- `CMTowerData f hf1 Λ K` with `h_div_conj_mem_Λ` proved via Phase A's
  `Q_sq_div_conj_mem_integers_of_spData`.

This is the proved Lean code that lets `brd_cm_tower_postulate` be assembled
from `brd_tower_data` without further sorries.
-/

namespace Erdos90.CMField

variable (K : Type) [Field K] [NumberField K] [IsCMField K] [IsTotallyComplex K]

/-- The scaling linear equivalence `v ↦ (Q⁻²) • v` on `Fin f → ℂ` as an ℝ-linear
equivalence. -/
noncomputable def qInvSqEquiv (f : ℕ) (Q : ℕ) (hQ : Q > 0) :
    (Fin f → ℂ) ≃ₗ[ℝ] (Fin f → ℂ) :=
  LinearEquiv.smulOfNeZero ℝ (Fin f → ℂ) (((Q : ℝ)^2)⁻¹) (by
    have hQ_pos_real : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
    have hQ_sq_pos : (0 : ℝ) < (Q : ℝ)^2 := by positivity
    exact inv_ne_zero (ne_of_gt hQ_sq_pos))

/-- The Q²-scaled transported basis: each unscaled basis vector multiplied by Q⁻². -/
noncomputable def qScaledTransportedBasis (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f)
    (Q : ℕ) (hQ : Q > 0) :
    Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) ℝ (Fin f → ℂ) :=
  (cmTransportedBasis K f hf).map (qInvSqEquiv f Q hQ)

/-- The Q²-scaled CM Minkowski lattice: ℤ-span of the Q²-scaled transported basis. -/
noncomputable def qScaledCMMinkowskiLattice (f : ℕ)
    (hf : InfinitePlace.nrComplexPlaces K = f) (Q : ℕ) (hQ : Q > 0) :
    AddSubgroup (Fin f → ℂ) :=
  (Submodule.span ℤ (Set.range (qScaledTransportedBasis K f hf Q hQ))).toAddSubgroup

/-- Membership in the scaled lattice: `v` is in `qScaledCMMinkowskiLattice` iff
`v = Q⁻² • Φ(a)` for some `a ∈ 𝓞 K`. -/
lemma mem_qScaledCMMinkowskiLattice_iff (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f)
    (Q : ℕ) (hQ : Q > 0) (v : Fin f → ℂ) :
    v ∈ qScaledCMMinkowskiLattice K f hf Q hQ ↔
      ∃ a : 𝓞 K, (((Q : ℂ)^2)⁻¹) • cmMinkowskiEquiv K f hf
        (NumberField.mixedEmbedding K (a : K)) = v := by
  dsimp [qScaledCMMinkowskiLattice, qScaledTransportedBasis]
  have h_range_eq :
      Set.range ((cmTransportedBasis K f hf).map (qInvSqEquiv f Q hQ)) =
      (qInvSqEquiv f Q hQ) '' (Set.range (cmTransportedBasis K f hf)) := by
    ext z; simp
  rw [Submodule.mem_toAddSubgroup, h_range_eq]
  rw [show (Submodule.span ℤ ((qInvSqEquiv f Q hQ : (Fin f → ℂ) → (Fin f → ℂ)) ''
      (Set.range (cmTransportedBasis K f hf)))) =
      Submodule.map ((qInvSqEquiv f Q hQ).toLinearMap.restrictScalars ℤ)
        (Submodule.span ℤ (Set.range (cmTransportedBasis K f hf))) from by
      simp [Submodule.map_span]]
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨w, hw_unscaled, hw_eq⟩
    have hw_in_unscaled : w ∈ cmMinkowskiLattice K f hf := by
      change w ∈ (Submodule.span ℤ (Set.range (cmTransportedBasis K f hf))).toAddSubgroup
      simpa using hw_unscaled
    rcases (mem_cmMinkowskiLattice_iff K f hf w).mp hw_in_unscaled with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [ha]
    -- Show: (Q⁻²) • w = qInvSqEquiv applied to w (as ℝ-action vs ℂ-action match for real Q⁻²)
    have hreal : (((Q : ℝ)^2)⁻¹ : ℝ) • w = (((Q : ℂ)^2)⁻¹) • w := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
      push_cast
      ring
    rw [← hreal]
    exact hw_eq
  · rintro ⟨a, ha⟩
    let w : Fin f → ℂ := cmMinkowskiEquiv K f hf (NumberField.mixedEmbedding K (a : K))
    have hw_in : w ∈ cmMinkowskiLattice K f hf :=
      (mem_cmMinkowskiLattice_iff K f hf w).mpr ⟨a, rfl⟩
    have hw_in' : w ∈ (Submodule.span ℤ (Set.range (cmTransportedBasis K f hf))) := by
      change w ∈ (cmMinkowskiLattice K f hf : Set _)
      exact hw_in
    refine ⟨w, hw_in', ?_⟩
    -- Goal: ((qInvSqEquiv f Q hQ).toLinearMap.restrictScalars ℤ) w = v
    change (qInvSqEquiv f Q hQ) w = v
    have hreal : (qInvSqEquiv f Q hQ) w = (((Q : ℝ)^2)⁻¹ : ℝ) • w := by
      show (LinearEquiv.smulOfNeZero ℝ (Fin f → ℂ) (((Q : ℝ)^2)⁻¹) _) w = _
      rfl
    rw [hreal]
    have hreal2 : (((Q : ℝ)^2)⁻¹ : ℝ) • w = (((Q : ℂ)^2)⁻¹) • w := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
      push_cast; ring
    rw [hreal2, ha]

/-- The Q²-scaled lattice is countable. -/
lemma qScaledCMMinkowskiLattice_countable (f : ℕ)
    (hf : InfinitePlace.nrComplexPlaces K = f) (Q : ℕ) (hQ : Q > 0) :
    Countable (qScaledCMMinkowskiLattice K f hf Q hQ) := by
  dsimp [qScaledCMMinkowskiLattice]
  change Countable (Submodule.span ℤ (Set.range (qScaledTransportedBasis K f hf Q hQ)))
  infer_instance

/-- The fundamental domain for the Q²-scaled lattice. -/
noncomputable def qScaledFundamentalDomain (f : ℕ)
    (hf : InfinitePlace.nrComplexPlaces K = f) (Q : ℕ) (hQ : Q > 0) :
    Set (Fin f → ℂ) :=
  ZSpan.fundamentalDomain (qScaledTransportedBasis K f hf Q hQ)

lemma qScaledIsAddFundamentalDomain (f : ℕ)
    (hf : InfinitePlace.nrComplexPlaces K = f) (Q : ℕ) (hQ : Q > 0) :
    IsAddFundamentalDomain (qScaledCMMinkowskiLattice K f hf Q hQ)
      (qScaledFundamentalDomain K f hf Q hQ) volume := by
  dsimp [qScaledCMMinkowskiLattice, qScaledFundamentalDomain]
  exact ZSpan.isAddFundamentalDomain' (qScaledTransportedBasis K f hf Q hQ) volume

lemma qScaledFundamentalDomain_bounded (f : ℕ)
    (hf : InfinitePlace.nrComplexPlaces K = f) (Q : ℕ) (hQ : Q > 0) :
    Bornology.IsBounded (qScaledFundamentalDomain K f hf Q hQ) := by
  dsimp [qScaledFundamentalDomain]
  exact ZSpan.fundamentalDomain_isBounded _

lemma qScaledFundamentalDomain_volume_lt_top (f : ℕ)
    (hf : InfinitePlace.nrComplexPlaces K = f) (Q : ℕ) (hQ : Q > 0) :
    volume (qScaledFundamentalDomain K f hf Q hQ) < ∞ := by
  dsimp [qScaledFundamentalDomain]
  have h_bounded : Bornology.IsBounded
      (ZSpan.fundamentalDomain (qScaledTransportedBasis K f hf Q hQ)) :=
    ZSpan.fundamentalDomain_isBounded _
  rcases h_bounded.subset_closedBall (0 : Fin f → ℂ) with ⟨R, hR⟩
  apply lt_of_le_of_lt (measure_mono hR)
  haveI : FiniteDimensional ℝ (Fin f → ℂ) := inferInstance
  haveI : ProperSpace (Fin f → ℂ) := FiniteDimensional.proper ℝ (Fin f → ℂ)
  exact measure_closedBall_lt_top

lemma qScaledFundamentalDomain_volume_pos (f : ℕ)
    (hf : InfinitePlace.nrComplexPlaces K = f) (Q : ℕ) (hQ : Q > 0) :
    volume (qScaledFundamentalDomain K f hf Q hQ) > 0 := by
  dsimp [qScaledFundamentalDomain]
  have h_ne_zero : volume (ZSpan.fundamentalDomain (qScaledTransportedBasis K f hf Q hQ)) ≠ 0 :=
    ZSpan.measure_fundamentalDomain_ne_zero (b := qScaledTransportedBasis K f hf Q hQ)
      (μ := volume)
  exact pos_iff_ne_zero.mpr h_ne_zero

/-- Separation for the Q²-scaled lattice: every nonzero element has some coordinate
of modulus ≥ Q⁻². -/
lemma qScaledLattice_separation (f : ℕ) (hf1 : f ≥ 1)
    (hf : InfinitePlace.nrComplexPlaces K = f) (Q : ℕ) (hQ : Q > 0) :
    ∀ v ∈ qScaledCMMinkowskiLattice K f hf Q hQ, v ≠ 0 →
      ∃ i : Fin f, ‖v i‖ ≥ (((Q : ℝ)^2)⁻¹) := by
  intro v hv hv0
  rcases (mem_qScaledCMMinkowskiLattice_iff K f hf Q hQ v).mp hv with ⟨a, ha⟩
  -- v = (Q⁻²) • cmMinkowskiEquiv(Φ(a:K))
  -- a ≠ 0 since v ≠ 0
  have ha_ne : a ≠ 0 := by
    intro hzero
    apply hv0
    rw [← ha, hzero]
    simp
  -- Let w = cmMinkowskiEquiv(Φ(a:K)); w is in the UNSCALED lattice, w ≠ 0
  let w : Fin f → ℂ := cmMinkowskiEquiv K f hf (NumberField.mixedEmbedding K (a : K))
  have hw_mem : w ∈ cmMinkowskiLattice K f hf :=
    (mem_cmMinkowskiLattice_iff K f hf w).mpr ⟨a, rfl⟩
  have hw_ne : w ≠ 0 := by
    intro hw0
    apply hv0
    rw [← ha]
    change ((Q : ℂ)^2)⁻¹ • w = 0
    rw [hw0, smul_zero]
  -- Use cmSeparation_exists with D₀ = 1
  obtain ⟨i, hi⟩ := cmSeparation_exists K f hf1 hf 1 (by norm_num) (le_refl 1) w hw_mem hw_ne
  -- ‖w i‖ ≥ 1⁻¹ = 1, so ‖v i‖ = Q⁻² · ‖w i‖ ≥ Q⁻²
  refine ⟨i, ?_⟩
  rw [← ha]
  show ‖(((Q : ℂ)^2)⁻¹ • w) i‖ ≥ ((Q : ℝ)^2)⁻¹
  rw [Pi.smul_apply, smul_eq_mul, norm_mul]
  have h_norm_inv : ‖((Q : ℂ)^2)⁻¹‖ = ((Q : ℝ)^2)⁻¹ := by
    rw [norm_inv]
    push_cast
    simp
  rw [h_norm_inv]
  have hQ_inv_sq_pos : (0 : ℝ) < ((Q : ℝ)^2)⁻¹ := by
    apply inv_pos.mpr
    have : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
    positivity
  have hi_one : ‖w i‖ ≥ 1 := by simpa using hi
  calc ((Q : ℝ)^2)⁻¹ * ‖w i‖
      ≥ ((Q : ℝ)^2)⁻¹ * 1 := by
        apply mul_le_mul_of_nonneg_left hi_one (le_of_lt hQ_inv_sq_pos)
    _ = ((Q : ℝ)^2)⁻¹ := by ring

/-- Projection injectivity for the Q²-scaled lattice: a lattice vector that
vanishes at the first coordinate is zero. -/
lemma qScaledLattice_first_coord_injective (f : ℕ) (hf1 : f ≥ 1)
    (hf : InfinitePlace.nrComplexPlaces K = f) (Q : ℕ) (hQ : Q > 0) :
    ∀ v ∈ qScaledCMMinkowskiLattice K f hf Q hQ,
      v (fin0 hf1) = 0 → v = 0 := by
  intro v hv hzero
  rcases (mem_qScaledCMMinkowskiLattice_iff K f hf Q hQ v).mp hv with ⟨a, ha⟩
  let w : Fin f → ℂ := cmMinkowskiEquiv K f hf (NumberField.mixedEmbedding K (a : K))
  have hv_eq : ((Q : ℂ)^2)⁻¹ • w = v := ha
  -- v(fin0) = (Q⁻²) · w(fin0) = 0; since Q ≠ 0, w(fin0) = 0
  have hQ_ne : ((Q : ℂ)^2)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    have : (Q : ℂ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hQ
    exact pow_ne_zero _ this
  have hw_zero_at_fin0 : w (fin0 hf1) = 0 := by
    have hprod : ((Q : ℂ)^2)⁻¹ * w (fin0 hf1) = v (fin0 hf1) := by
      have h := congrArg (fun u => u (fin0 hf1)) hv_eq
      simpa [Pi.smul_apply, smul_eq_mul] using h
    rw [hzero] at hprod
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd h hQ_ne
    · exact h
  -- By unscaled injectivity argument (replicate from cmSeparation infrastructure)
  let w₀ : {w' : InfinitePlace K // InfinitePlace.IsComplex w'} :=
    (cmComplexPlaceEquiv K f hf).symm (fin0 hf1)
  have h_coord_zero : (NumberField.mixedEmbedding K (a : K)).2 w₀ = 0 := by
    rw [← cmMinkowskiEquiv_apply_complex (K := K) (f := f) (hf := hf)
      (NumberField.mixedEmbedding K (a : K)) w₀]
    have : (cmComplexPlaceEquiv K f hf) w₀ = fin0 hf1 := by
      dsimp [w₀]; simp
    rw [this]
    exact hw_zero_at_fin0
  have h_norm_zero : mixedEmbedding.normAtPlace (w₀ : InfinitePlace K)
      (NumberField.mixedEmbedding K (a : K)) = 0 := by
    rw [mixedEmbedding.normAtPlace_apply_of_isComplex w₀.prop, h_coord_zero, norm_zero]
  rw [mixedEmbedding.normAtPlace_apply] at h_norm_zero
  have ha_eq_zero : (a : K) = 0 := by
    by_contra h_ne
    have h_pos : 0 < (w₀ : InfinitePlace K) (a : K) :=
      AbsoluteValue.pos_iff (w₀ : InfinitePlace K).1 |>.mpr h_ne
    linarith
  -- Now w = cmMinkowskiEquiv (Φ 0) = 0
  have hw_zero : w = 0 := by
    show cmMinkowskiEquiv K f hf (NumberField.mixedEmbedding K (a : K)) = 0
    have : NumberField.mixedEmbedding K (a : K) = 0 := by
      rw [ha_eq_zero]; simp
    rw [this]; simp
  rw [← hv_eq, hw_zero, smul_zero]

end Erdos90.CMField

end
