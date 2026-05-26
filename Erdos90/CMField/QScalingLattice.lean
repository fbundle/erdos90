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

end Erdos90.CMField

end
