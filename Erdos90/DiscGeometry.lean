import Mathlib
import Erdos90.Defs
import Erdos90.Arithmetic

open Real Filter NumberField Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal Topology Complex intervalIntegral Pointwise

noncomputable section

/-!
# Disc geometry lemmas supporting Lemma 2.4

Geometric and measure-theoretic results about disc intersections and polydiscs,
used in the coset averaging argument (see CosetAveraging.lean).
-/

/-- The polydisc is a measurable set (intersection of closed balls). -/
lemma polydisc_measurable (f : ℕ) (R : ℝ) : MeasurableSet (polydisc f R) := by
  have : polydisc f R = ⋂ (r : Fin f), {x | ‖x r‖ ≤ R} := by
    ext x; simp [polydisc]
  rw [this]
  refine MeasurableSet.iInter fun r => ?_
  exact isClosed_le (by continuity) continuous_const |>.measurableSet

/-- **Positivity of the disc intersection area.** For R > 1/2, the numerator
    a(R) = 2R²·arccos(1/(2R)) − (1/2)·√(4R²−1) is positive.
    Proof via trigonometric substitution θ = arccos(1/(2R)) and sin θ < θ. -/
lemma a_pos (R : ℝ) (hR : R > 1/2) : 2*R^2*Real.arccos (1/(2*R)) - (1/2)*Real.sqrt (4*R^2-1) > 0 := by
  have hRpos : R > 0 := by linarith
  have h_2R_gt_1 : 2*R > 1 := by linarith
  have h_inv_pos : 0 < 1/(2*R) := div_pos (by norm_num) (by linarith)
  have h_inv_lt_one : 1/(2*R) < 1 := (div_lt_one (by nlinarith)).mpr h_2R_gt_1
  have h_4R2_gt_1 : 4*R^2 - 1 > 0 := by nlinarith
  set θ := Real.arccos (1/(2*R))
  have hθ_pos : 0 < θ := Real.arccos_pos.mpr h_inv_lt_one
  have hθ_lt_pi_div_two : θ < π/2 := Real.arccos_lt_pi_div_two.mpr h_inv_pos
  have hθ_lt_pi : θ < π := by linarith
  have h_sin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
  have h_cos_pos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ_lt_pi_div_two⟩
  have h_cos_θ : Real.cos θ = 1/(2*R) :=
    Real.cos_arccos (by
      have : 0 < 2*R := by linarith
      have : 0 ≤ 1/(2*R) := div_nonneg (by norm_num) (by linarith)
      linarith) (by linarith)
  have h_sin_θ : Real.sin θ = Real.sqrt (4*R^2-1) / (2*R) := by
    calc
      Real.sin θ = Real.sqrt (1 - (1/(2*R))^2) := Real.sin_arccos _
      _ = Real.sqrt ((4*R^2-1) / (4*R^2)) := by
        congr
        field_simp [hRpos.ne.symm]
        ring
      _ = Real.sqrt (4*R^2-1) / Real.sqrt (4*R^2) := Real.sqrt_div (by nlinarith) _
      _ = Real.sqrt (4*R^2-1) / (2*R) := by rw [show (4 : ℝ)*R^2 = ((2*R)^2) by ring, Real.sqrt_sq (by linarith : 0 ≤ 2*R)]
  -- Key identity: a(R) = R · (2R·θ − sin θ) = R · (θ − sin θ·cos θ) / cos θ
  have h_a_eq : 2*R^2*θ - (1/2)*Real.sqrt (4*R^2-1) = R*(θ - Real.sin θ*Real.cos θ)/Real.cos θ := by
    rw [h_sin_θ, h_cos_θ]
    field_simp [hRpos.ne.symm]
  rw [h_a_eq]
  have h_num : 0 < θ - Real.sin θ * Real.cos θ := by
    have h_sin_lt_θ : Real.sin θ < θ := Real.sin_lt hθ_pos
    have h_cos_le_one : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have h_sin_cos_le_sin : Real.sin θ * Real.cos θ ≤ Real.sin θ := by
      nlinarith
    nlinarith
  positivity

/-- Antiderivative of `2·√(R²−x²)`: `F(x) = R²·arcsin(x/R) + x·√(R²−x²)`
    satisfies `F'(x) = 2·√(R²−x²)` on `(-R,R)` for `R > 0`.
    Adapted directly from `Theorems100.area_disc`. -/
lemma hasDerivAt_intersect_antideriv (R x : ℝ) (hR : R > 0) (hx : x ∈ Ioo (-R) R) :
    HasDerivAt (fun y => R ^ 2 * Real.arcsin (R⁻¹ * y) + y * Real.sqrt (R ^ 2 - y ^ 2))
      (2 * Real.sqrt (R ^ 2 - x ^ 2)) x := by
  set f := fun y : ℝ => Real.sqrt (R ^ 2 - y ^ 2) with hf
  set F := fun y : ℝ => R ^ 2 * Real.arcsin (R⁻¹ * y) + y * f y with hF
  have h_sq_pos : 0 < R ^ 2 - x ^ 2 := sub_pos_of_lt (sq_lt_sq' hx.1 hx.2)
  have h_sq_pos' : R ^ 2 - x ^ 2 ≠ 0 := by linarith
  have hderiv : HasDerivAt F (2 * f x) x := by
    rw [hF, hf]
    have h_as1 : R⁻¹ * x ≠ -1 := by
      intro h
      have : x = -R := by
        calc
          x = R * (R⁻¹ * x) := by field_simp [hR.ne.symm]
          _ = R * (-1) := by rw [h]
          _ = -R := by ring
      rw [this] at hx; exact lt_irrefl _ hx.1
    have h_as2 : R⁻¹ * x ≠ 1 := by
      intro h
      have : x = R := by
        calc
          x = R * (R⁻¹ * x) := by field_simp [hR.ne.symm]
          _ = R * 1 := by rw [h]
          _ = R := by ring
      rw [this] at hx; exact lt_irrefl _ hx.2
    convert
      (((hasDerivAt_const x (R ^ 2)).mul
          ((hasDerivAt_arcsin h_as1 h_as2).comp x
            ((hasDerivAt_const x R⁻¹).mul (hasDerivAt_id' x)))).add
        ((hasDerivAt_id' x).mul ((((hasDerivAt_id' x).fun_pow 2).const_sub (R ^ 2)).sqrt
          h_sq_pos')))
      using 1
    · -- algebraic simplification of the derivative expression
      have h_cube : f x ^ 3 = (R ^ 2 - x ^ 2) * f x := by
        rw [hf, pow_three, ← mul_assoc, mul_self_sqrt (by positivity)]
      simp
      field_simp
      simp (disch := positivity)
      field_simp
      ring
  simpa [hf] using hderiv

/-- The circle `{p | p.1²+p.2² = R²}` in ℝ×ℝ has Lebesgue measure zero.
    Transfers the fact that spheres in ℂ have zero measure. -/
lemma volume_circle_eq_zero (R : ℝ) :
    volume {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = R ^ 2} = 0 := by
  let e : ℝ × ℝ ≃ᵐ ℂ := Complex.measurableEquivRealProd.symm
  have h_pres : MeasurePreserving (e : ℝ × ℝ → ℂ) :=
    Complex.volume_preserving_equiv_real_prod.symm
  have h_sphere : volume (Metric.sphere (0 : ℂ) |R|) = 0 := addHaar_sphere volume (0 : ℂ) |R|
  have h_preimage : (e : ℝ × ℝ → ℂ) ⁻¹' Metric.sphere (0 : ℂ) |R| =
      {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = R ^ 2} := by
    ext ⟨x, y⟩
    simp only [e, Complex.measurableEquivRealProd_symm_apply, Set.mem_preimage, Set.mem_setOf_eq]
    rw [Metric.mem_sphere, Complex.dist_eq, sub_zero]
    have h_norm_iff : ‖({ re := x, im := y } : ℂ)‖ = |R| ↔ x ^ 2 + y ^ 2 = R ^ 2 := by
      have h_norm_sq : Complex.normSq ({ re := x, im := y } : ℂ) = x ^ 2 + y ^ 2 := by
        simp [Complex.normSq_apply, sq]
      constructor
      · intro h
        have h_sq : ‖({ re := x, im := y } : ℂ)‖ ^ 2 = |R| ^ 2 := by rw [h]
        rw [← Complex.normSq_eq_norm_sq, h_norm_sq] at h_sq
        rw [sq_abs] at h_sq
        exact h_sq
      · intro h
        have h_sq : Complex.normSq ({ re := x, im := y } : ℂ) = R ^ 2 := by rw [h_norm_sq, h]
        have h_sq' : ‖({ re := x, im := y } : ℂ)‖ ^ 2 = R ^ 2 := by rwa [← Complex.normSq_eq_norm_sq]
        have h_sq'' : ‖({ re := x, im := y } : ℂ)‖ ^ 2 = |R| ^ 2 := by rw [sq_abs R, h_sq']
        exact (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp h_sq''
    exact h_norm_iff
  rw [← h_preimage, h_pres.measure_preimage_equiv, h_sphere]

/-- A shifted circle `{p | (p.1 + c)² + p.2² = R²}` also has measure zero. -/
lemma volume_shifted_circle_eq_zero (c R : ℝ) :
    volume {p : ℝ × ℝ | (p.1 + c) ^ 2 + p.2 ^ 2 = R ^ 2} = 0 := by
  let e : ℝ × ℝ ≃ᵐ ℂ := Complex.measurableEquivRealProd.symm
  have h_pres : MeasurePreserving (e : ℝ × ℝ → ℂ) :=
    Complex.volume_preserving_equiv_real_prod.symm
  have h_sphere : volume (Metric.sphere (-c : ℂ) |R|) = 0 := addHaar_sphere volume (-c : ℂ) |R|
  have h_preimage : (e : ℝ × ℝ → ℂ) ⁻¹' Metric.sphere (-c : ℂ) |R| =
      {p : ℝ × ℝ | (p.1 + c) ^ 2 + p.2 ^ 2 = R ^ 2} := by
    ext ⟨x, y⟩
    simp only [e, Complex.measurableEquivRealProd_symm_apply, Set.mem_preimage, Set.mem_setOf_eq]
    rw [Metric.mem_sphere, Complex.dist_eq]
    have h_norm_iff : ‖({ re := x, im := y } : ℂ) - (-c : ℂ)‖ = |R| ↔ (x + c) ^ 2 + y ^ 2 = R ^ 2 := by
      have h_norm_sq : Complex.normSq (({ re := x, im := y } : ℂ) - (-c : ℂ)) =
          (x + c) ^ 2 + y ^ 2 := by
        simp [Complex.normSq_apply, sq]
      constructor
      · intro h
        have h_sq : ‖({ re := x, im := y } : ℂ) - (-c : ℂ)‖ ^ 2 = |R| ^ 2 := by rw [h]
        rw [← Complex.normSq_eq_norm_sq, h_norm_sq] at h_sq
        rw [sq_abs R] at h_sq
        exact h_sq
      · intro h
        have h_sq : Complex.normSq (({ re := x, im := y } : ℂ) - (-c : ℂ)) = R ^ 2 := by
          rw [h_norm_sq, h]
        have h_sq' : ‖({ re := x, im := y } : ℂ) - (-c : ℂ)‖ ^ 2 = R ^ 2 := by
          rwa [← Complex.normSq_eq_norm_sq]
        have h_sq'' : ‖({ re := x, im := y } : ℂ) - (-c : ℂ)‖ ^ 2 = |R| ^ 2 := by
          rw [sq_abs R, h_sq']
        exact (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp h_sq''
    exact h_norm_iff
  rw [← h_preimage, h_pres.measure_preimage_equiv, h_sphere]

/-- Algebraic simplification: (F(-1/2)-F(-R)) + (F(R)-F(1/2)) = a(R)
    where F(x) = R²·arcsin(x/R) + x·√(R²−x²).  Extracted from `lens_volume_eq_aR`. -/
lemma antideriv_lens_eq_aR (R : ℝ) (hR : R > 1/2) :
    (R ^ 2 * Real.arcsin (R⁻¹ * (-(1/2))) + (-(1/2)) * Real.sqrt (R ^ 2 - (-(1/2)) ^ 2) -
     (R ^ 2 * Real.arcsin (R⁻¹ * (-R)) + (-R) * Real.sqrt (R ^ 2 - (-R) ^ 2))) +
    (R ^ 2 * Real.arcsin (R⁻¹ * R) + R * Real.sqrt (R ^ 2 - R ^ 2) -
     (R ^ 2 * Real.arcsin (R⁻¹ * (1/2)) + (1/2) * Real.sqrt (R ^ 2 - (1/2) ^ 2))) =
    2 * R ^ 2 * Real.arccos (1 / (2 * R)) - (1 / 2) * Real.sqrt (4 * R ^ 2 - 1) := by
  have hRpos : R > 0 := by linarith
  have h_sqrt_zero : Real.sqrt (R ^ 2 - R ^ 2) = 0 := by simp
  have h_sqrt_negR_zero : Real.sqrt (R ^ 2 - (-R) ^ 2) = 0 := by
    simp
  have h_sqrt_half : Real.sqrt (R ^ 2 - (1/2 : ℝ) ^ 2) = Real.sqrt (4 * R ^ 2 - 1) / 2 := by
    calc
      Real.sqrt (R ^ 2 - (1/2 : ℝ) ^ 2) = Real.sqrt ((4 * R ^ 2 - 1) / 4) := by ring_nf
      _ = Real.sqrt (4 * R ^ 2 - 1) / Real.sqrt 4 := Real.sqrt_div (by nlinarith) _
      _ = Real.sqrt (4 * R ^ 2 - 1) / 2 := by norm_num
  have h_sqrt_neg_half : Real.sqrt (R ^ 2 - (-(1/2 : ℝ)) ^ 2) = Real.sqrt (4 * R ^ 2 - 1) / 2 := by
    calc
      Real.sqrt (R ^ 2 - (-(1/2 : ℝ)) ^ 2) = Real.sqrt (R ^ 2 - (1/2 : ℝ) ^ 2) := by norm_num
      _ = Real.sqrt (4 * R ^ 2 - 1) / 2 := h_sqrt_half
  have h_inv_half : R⁻¹ * (1/2 : ℝ) = (2 * R)⁻¹ := by
    field_simp [hRpos.ne.symm]
  have h_arcsin_R : Real.arcsin (R⁻¹ * R) = π / 2 := by
    simp [hRpos.ne.symm, Real.arcsin_one]
  have h_arcsin_negR : Real.arcsin (R⁻¹ * (-R)) = -(π / 2) := by
    simp [hRpos.ne.symm]
  have h_arcsin_half : Real.arcsin (R⁻¹ * (1/2 : ℝ)) = Real.arcsin ((2 * R)⁻¹) := by
    rw [h_inv_half]
  have h_arcsin_neg_half : Real.arcsin (R⁻¹ * (-(1/2 : ℝ))) = -Real.arcsin ((2 * R)⁻¹) := by
    calc
      Real.arcsin (R⁻¹ * (-(1/2 : ℝ))) = Real.arcsin (-(R⁻¹ * (1/2 : ℝ))) := by ring_nf
      _ = -Real.arcsin (R⁻¹ * (1/2 : ℝ)) := by rw [Real.arcsin_neg]
      _ = -Real.arcsin ((2 * R)⁻¹) := by rw [h_inv_half]
  have h_arcsin_to_arccos : Real.arcsin ((2 * R)⁻¹) = π / 2 - Real.arccos (1 / (2 * R)) := by
    rw [show ((2 : ℝ) * R)⁻¹ = 1 / (2 * R) by field_simp [hRpos.ne.symm]]
    rw [Real.arcsin_eq_pi_div_two_sub_arccos]
  calc
    (R ^ 2 * Real.arcsin (R⁻¹ * (-(1/2))) + (-(1/2)) * Real.sqrt (R ^ 2 - (-(1/2)) ^ 2) -
     (R ^ 2 * Real.arcsin (R⁻¹ * (-R)) + (-R) * Real.sqrt (R ^ 2 - (-R) ^ 2))) +
    (R ^ 2 * Real.arcsin (R⁻¹ * R) + R * Real.sqrt (R ^ 2 - R ^ 2) -
     (R ^ 2 * Real.arcsin (R⁻¹ * (1/2)) + (1/2) * Real.sqrt (R ^ 2 - (1/2) ^ 2)))
    = (R ^ 2 * (-Real.arcsin ((2 * R)⁻¹)) + (-(1/2)) * (Real.sqrt (4 * R ^ 2 - 1) / 2) -
       (R ^ 2 * (-(π / 2)) + (-R) * 0)) +
      (R ^ 2 * (π / 2) + R * 0 -
       (R ^ 2 * Real.arcsin ((2 * R)⁻¹) + (1/2) * (Real.sqrt (4 * R ^ 2 - 1) / 2))) := by
      rw [h_sqrt_zero, h_sqrt_negR_zero, h_sqrt_half, h_sqrt_neg_half, h_arcsin_R,
        h_arcsin_negR, h_arcsin_half, h_arcsin_neg_half]
    _ = 2 * R ^ 2 * Real.arccos (1 / (2 * R)) - (1 / 2) * Real.sqrt (4 * R ^ 2 - 1) := by
      rw [h_arcsin_to_arccos]
      ring

set_option maxHeartbeats 1000000 in
/-- **Lens volume = a(R).** For the special case u = 1 in ℝ×ℝ,
    the volume of {p | p.1²+p.2² ≤ R² ∧ (p.1+1)²+p.2² ≤ R²} equals a(R).
    The proof uses `regionBetween` and FTC following the AreaOfACircle pattern,
    with a null-boundary argument to bridge open and closed sets. -/
lemma lens_volume_eq_aR (R : ℝ) (hR : R > 1/2) :
    (volume {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ R ^ 2 ∧ (p.1 + 1) ^ 2 + p.2 ^ 2 ≤ R ^ 2}).toReal =
    2 * R ^ 2 * Real.arccos (1 / (2 * R)) - (1 / 2) * Real.sqrt (4 * R ^ 2 - 1) := by
  have hRpos : R > 0 := by linarith
  have h4R2_gt_1 : 4 * R ^ 2 - 1 > 0 := by nlinarith
  set f := fun x : ℝ => Real.sqrt (R ^ 2 - x ^ 2) with hf_def
  set g := fun x : ℝ => Real.sqrt (R ^ 2 - (x + 1) ^ 2) with hg_def
  set F := fun x : ℝ => R ^ 2 * Real.arcsin (R⁻¹ * x) + x * Real.sqrt (R ^ 2 - x ^ 2) with hF_def
  set L := {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ R ^ 2 ∧ (p.1 + 1) ^ 2 + p.2 ^ 2 ≤ R ^ 2} with hL_def
  set S_left := regionBetween (-f) f (Ioc (-R) (-(1/2))) with hS_left_def
  set S_right := regionBetween (-g) g (Ioc (-(1/2)) (R - 1)) with hS_right_def
  set N := {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = R ^ 2} ∪ {p : ℝ × ℝ | (p.1 + 1) ^ 2 + p.2 ^ 2 = R ^ 2} with hN_def
  -- Continuity and measurability
  have hf_cont : Continuous f := by unfold f; fun_prop
  have hg_cont : Continuous g := by unfold g; fun_prop
  have hF_cont : Continuous F := by unfold F; fun_prop
  have hf_meas : Measurable f := hf_cont.measurable
  have hg_meas : Measurable g := hg_cont.measurable
  have hf_nonneg : ∀ x, 0 ≤ f x := fun x => Real.sqrt_nonneg _
  have hg_nonneg : ∀ x, 0 ≤ g x := fun x => Real.sqrt_nonneg _
  -- Integrability on Ioc intervals
  have hf_int_on (a b : ℝ) : IntegrableOn f (Ioc a b) :=
    hf_cont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hg_int_on (a b : ℝ) : IntegrableOn g (Ioc a b) :=
    hg_cont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  -- Measurability of regionBetween sets
  have hS_left_meas : MeasurableSet S_left :=
    measurableSet_regionBetween hf_meas.neg hf_meas measurableSet_Ioc
  have hS_right_meas : MeasurableSet S_right :=
    measurableSet_regionBetween hg_meas.neg hg_meas measurableSet_Ioc
  -- Disjointness: S_left ∩ S_right = ∅ because x-intervals are disjoint
  have h_disjoint : Disjoint S_left S_right := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext ⟨x, y⟩
    constructor
    · intro h
      rcases h with ⟨⟨⟨hxl1, hxl2⟩, _⟩, ⟨⟨hxr1, hxr2⟩, _⟩⟩
      linarith
    · intro h; exact h.elim
  -- Ioc union identity: (-R, R-1] = (-R, -1/2] ∪ (-1/2, R-1]
  have h_Ioc_union : Ioc (-R) (-(1/2 : ℝ)) ∪ Ioc (-(1/2 : ℝ)) (R - 1) = Ioc (-R) (R - 1) := by
    ext x; constructor
    · intro h; rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, le_trans h2 (by linarith)⟩
      · exact ⟨by linarith, h2⟩
    · intro h; rcases h with ⟨h1, h2⟩
      by_cases hx : x ≤ -(1/2 : ℝ)
      · exact Or.inl ⟨h1, hx⟩
      · exact Or.inr ⟨by linarith, h2⟩
  -- Helper: f(x)^2 = R^2 - x^2 when x^2 ≤ R^2
  have hf_sq (x : ℝ) (hx2 : x ^ 2 ≤ R ^ 2) : f x ^ 2 = R ^ 2 - x ^ 2 := by
    unfold f; rw [Real.sq_sqrt (by nlinarith)]
  -- Helper: g(x)^2 = R^2 - (x+1)^2 when (x+1)^2 ≤ R^2
  have hg_sq (x : ℝ) (hx2 : (x + 1) ^ 2 ≤ R ^ 2) : g x ^ 2 = R ^ 2 - (x + 1) ^ 2 := by
    unfold g; rw [Real.sq_sqrt (by nlinarith)]
  -- f ≤ g when x ≤ -1/2; g ≤ f when x ≥ -1/2
  have hf_le_g (x : ℝ) (hx : x ≤ -(1/2 : ℝ)) : f x ≤ g x := by
    unfold f g; refine Real.sqrt_le_sqrt ?_; nlinarith
  have hg_le_f (x : ℝ) (hx : -(1/2 : ℝ) ≤ x) : g x ≤ f x := by
    unfold f g; refine Real.sqrt_le_sqrt ?_; nlinarith
  -- S_left ∪ S_right ⊆ L
  have h_union_sub_L : S_left ∪ S_right ⊆ L := by
    intro p hp
    rcases hp with (hp | hp)
    · -- p ∈ S_left
      rcases hp with ⟨⟨hxl, hxr⟩, hy⟩
      rcases hy with ⟨hyl, hyr⟩
      have hx_sq_le : p.1 ^ 2 ≤ R ^ 2 := by
        have : |p.1| ≤ R := by
          have hxl' : -R ≤ p.1 := by linarith
          have hxr' : p.1 ≤ R := by linarith
          exact abs_le.mpr ⟨by linarith, by linarith⟩
        nlinarith [sq_abs p.1]
      have hpy_sq_lt_fsq : p.2 ^ 2 < f p.1 ^ 2 := by
        have habs : |p.2| < f p.1 := abs_lt.mpr ⟨hyl, hyr⟩
        have h_abs_f : |f p.1| = f p.1 := abs_of_nonneg (hf_nonneg _)
        have habs' : |p.2| < |f p.1| := by rwa [h_abs_f]
        exact (sq_lt_sq (a := p.2) (b := f p.1)).mpr habs'
      have hf_sq_eq : f p.1 ^ 2 = R ^ 2 - p.1 ^ 2 := hf_sq p.1 hx_sq_le
      rw [hf_sq_eq] at hpy_sq_lt_fsq
      have hx1_sq_le : (p.1 + 1) ^ 2 ≤ R ^ 2 := by
        have : (p.1 + 1) ^ 2 ≤ p.1 ^ 2 := by nlinarith
        nlinarith
      have hpy_sq_lt_gsq : p.2 ^ 2 < g p.1 ^ 2 := by
        have habs : |p.2| < g p.1 := by
          have h_fg : f p.1 ≤ g p.1 := hf_le_g p.1 hxr
          have habs_f : |p.2| < f p.1 := abs_lt.mpr ⟨hyl, hyr⟩
          linarith
        have h_abs_g : |g p.1| = g p.1 := abs_of_nonneg (hg_nonneg _)
        have habs' : |p.2| < |g p.1| := by rwa [h_abs_g]
        exact (sq_lt_sq (a := p.2) (b := g p.1)).mpr habs'
      have hg_sq_eq : g p.1 ^ 2 = R ^ 2 - (p.1 + 1) ^ 2 := hg_sq p.1 hx1_sq_le
      rw [hg_sq_eq] at hpy_sq_lt_gsq
      have h1 : p.1 ^ 2 + p.2 ^ 2 ≤ R ^ 2 := by nlinarith
      have h2 : (p.1 + 1) ^ 2 + p.2 ^ 2 ≤ R ^ 2 := by nlinarith
      exact ⟨h1, h2⟩
    · -- p ∈ S_right
      rcases hp with ⟨⟨hxl, hxr⟩, hy⟩
      rcases hy with ⟨hyl, hyr⟩
      have hx1_sq_le : (p.1 + 1) ^ 2 ≤ R ^ 2 := by
        have : |p.1 + 1| ≤ R := by
          have hxl' : -R ≤ p.1 + 1 := by linarith
          have hxr' : p.1 + 1 ≤ R := by linarith
          exact abs_le.mpr ⟨by linarith, by linarith⟩
        nlinarith [sq_abs (p.1 + 1)]
      have hpy_sq_lt_gsq : p.2 ^ 2 < g p.1 ^ 2 := by
        have habs : |p.2| < g p.1 := abs_lt.mpr ⟨hyl, hyr⟩
        have h_abs_g : |g p.1| = g p.1 := abs_of_nonneg (hg_nonneg _)
        have habs' : |p.2| < |g p.1| := by rwa [h_abs_g]
        exact (sq_lt_sq (a := p.2) (b := g p.1)).mpr habs'
      have hg_sq_eq : g p.1 ^ 2 = R ^ 2 - (p.1 + 1) ^ 2 := hg_sq p.1 hx1_sq_le
      rw [hg_sq_eq] at hpy_sq_lt_gsq
      have hx_sq_le : p.1 ^ 2 ≤ R ^ 2 := by
        have : p.1 ^ 2 ≤ (p.1 + 1) ^ 2 := by nlinarith
        nlinarith
      have hpy_sq_lt_fsq : p.2 ^ 2 < f p.1 ^ 2 := by
        have habs : |p.2| < f p.1 := by
          have h_gf : g p.1 ≤ f p.1 := hg_le_f p.1 (by linarith)
          have habs_g : |p.2| < g p.1 := abs_lt.mpr ⟨hyl, hyr⟩
          linarith
        have h_abs_f : |f p.1| = f p.1 := abs_of_nonneg (hf_nonneg _)
        have habs' : |p.2| < |f p.1| := by rwa [h_abs_f]
        exact (sq_lt_sq (a := p.2) (b := f p.1)).mpr habs'
      have hf_sq_eq : f p.1 ^ 2 = R ^ 2 - p.1 ^ 2 := hf_sq p.1 hx_sq_le
      rw [hf_sq_eq] at hpy_sq_lt_fsq
      have h1 : p.1 ^ 2 + p.2 ^ 2 ≤ R ^ 2 := by nlinarith
      have h2 : (p.1 + 1) ^ 2 + p.2 ^ 2 ≤ R ^ 2 := by nlinarith
      exact ⟨h1, h2⟩
  -- L \ (S_left ∪ S_right) ⊆ N
  have h_diff_sub_N : L \ (S_left ∪ S_right) ⊆ N := by
    intro p hp
    rcases hp with ⟨⟨hpL1, hpL2⟩, hp_not_union⟩
    by_cases h_eq1 : p.1 ^ 2 + p.2 ^ 2 = R ^ 2
    · exact Set.mem_union_left _ h_eq1
    · by_cases h_eq2 : (p.1 + 1) ^ 2 + p.2 ^ 2 = R ^ 2
      · exact Set.mem_union_right _ h_eq2
      · -- Both inequalities are strict
        have h_lt1 : p.1 ^ 2 + p.2 ^ 2 < R ^ 2 := lt_of_le_of_ne hpL1 h_eq1
        have h_lt2 : (p.1 + 1) ^ 2 + p.2 ^ 2 < R ^ 2 := lt_of_le_of_ne hpL2 h_eq2
        -- From strict inequalities, p.1 ∈ (-R, R-1)
        have hx_left : -R < p.1 := by
          by_contra! h; nlinarith
        have hx_right : p.1 < R - 1 := by
          by_contra! h; nlinarith
        -- Also p.1^2 ≤ R^2, (p.1+1)^2 ≤ R^2
        have hx_sq_le : p.1 ^ 2 ≤ R ^ 2 := by nlinarith
        have hx1_sq_le : (p.1 + 1) ^ 2 ≤ R ^ 2 := by nlinarith
        -- |p.2| < f(p.1) and |p.2| < g(p.1)
        have hy_sq_lt_f_sq : p.2 ^ 2 < f p.1 ^ 2 := by
          rw [hf_sq p.1 hx_sq_le]; nlinarith
        have hy_sq_lt_g_sq : p.2 ^ 2 < g p.1 ^ 2 := by
          rw [hg_sq p.1 hx1_sq_le]; nlinarith
        have hy_abs_lt_f : |p.2| < f p.1 :=
          abs_lt_of_sq_lt_sq hy_sq_lt_f_sq (hf_nonneg _)
        have hy_abs_lt_g : |p.2| < g p.1 :=
          abs_lt_of_sq_lt_sq hy_sq_lt_g_sq (hg_nonneg _)
        have hy_Ioo_f : p.2 ∈ Ioo (-f p.1) (f p.1) := by
          rcases abs_lt.mp hy_abs_lt_f with ⟨hlo, hhi⟩
          exact ⟨hlo, hhi⟩
        have hy_Ioo_g : p.2 ∈ Ioo (-g p.1) (g p.1) := by
          rcases abs_lt.mp hy_abs_lt_g with ⟨hlo, hhi⟩
          exact ⟨hlo, hhi⟩
        -- p.1 is in the union of the two Ioc intervals
        have hx_in_union : p.1 ∈ Ioc (-R) (-(1/2)) ∪ Ioc (-(1/2)) (R - 1) := by
          rw [h_Ioc_union]
          exact ⟨hx_left, by linarith⟩
        rcases hx_in_union with (hx_mem | hx_mem)
        · exfalso; apply hp_not_union
          apply Set.mem_union_left
          exact ⟨hx_mem, hy_Ioo_f⟩
        · exfalso; apply hp_not_union
          apply Set.mem_union_right
          exact ⟨hx_mem, hy_Ioo_g⟩
  -- N has measure zero (union of two circles)
  have hN_null : volume N = 0 := by
    rw [hN_def]
    have h1 : volume {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = R ^ 2} = 0 := volume_circle_eq_zero R
    have h2 : volume {p : ℝ × ℝ | (p.1 + 1) ^ 2 + p.2 ^ 2 = R ^ 2} = 0 := volume_shifted_circle_eq_zero 1 R
    refine le_antisymm ((measure_union_le _ _).trans ?_) (by simp)
    rw [h1, h2]
    simp
  -- a.e. equality: L and S_left ∪ S_right differ only on N (null)
  have hL_meas : MeasurableSet L := by
    rw [hL_def]
    have h_cont1 : Continuous (fun (p : ℝ × ℝ) => p.1 ^ 2 + p.2 ^ 2) := by continuity
    have h_cont2 : Continuous (fun (_ : ℝ × ℝ) => R ^ 2) := continuous_const
    have h_cont3 : Continuous (fun (p : ℝ × ℝ) => (p.1 + 1) ^ 2 + p.2 ^ 2) := by continuity
    refine ((isClosed_le h_cont1 h_cont2).inter
      (isClosed_le h_cont3 h_cont2)).measurableSet
  have h_union_meas : MeasurableSet (S_left ∪ S_right) :=
    hS_left_meas.union hS_right_meas
  have h_vol_eq : volume L = volume (S_left ∪ S_right) := by
    have h1 : volume (L \ (S_left ∪ S_right)) = 0 := measure_mono_null h_diff_sub_N hN_null
    have h2 : volume ((S_left ∪ S_right) \ L) = 0 := by
      have h_empty : (S_left ∪ S_right) \ L = ∅ := Set.diff_eq_empty.mpr h_union_sub_L
      rw [h_empty, measure_empty]
    have hL_eq := measure_inter_add_diff (μ := volume) L h_union_meas
    rw [h1, add_zero] at hL_eq
    have hU_eq := measure_inter_add_diff (μ := volume) (S_left ∪ S_right) hL_meas
    rw [h2, add_zero] at hU_eq
    rw [← hL_eq, ← hU_eq, Set.inter_comm]
  have h_vol_union : volume (S_left ∪ S_right) = volume S_left + volume S_right :=
    measure_union (μ := volume) h_disjoint hS_right_meas
  -- Volume of S_left via regionBetween formula
  have h_vol_left_raw : volume S_left = ENNReal.ofReal (∫ x in Ioc (-R) (-(1/2)), (f - (-f)) x) :=
    volume_regionBetween_eq_integral ((hf_int_on (-R) (-(1/2))).neg) (hf_int_on (-R) (-(1/2)))
      measurableSet_Ioc (fun x _ => by
        dsimp
        have h := hf_nonneg x
        linarith)
  have h_integrand_simp (x : ℝ) : (f - (-f)) x = 2 * f x := by
    simp [Pi.sub_apply, Pi.neg_apply, two_mul]
  have h_vol_left : (volume S_left).toReal = (∫ x in (-R : ℝ)..(-(1/2)), 2 * f x) := by
    rw [h_vol_left_raw, ENNReal.toReal_ofReal (integral_nonneg (by
      intro x; rw [h_integrand_simp x]; positivity))]
    have h_fun_eq : (f - (-f)) = (fun x => 2 * f x) := by
      ext x; rw [h_integrand_simp x]
    rw [h_fun_eq, ← intervalIntegral.integral_of_le (by linarith : (-R : ℝ) ≤ -(1/2))]
  -- Volume of S_right via regionBetween formula
  have h_vol_right_raw : volume S_right = ENNReal.ofReal (∫ x in Ioc (-(1/2)) (R - 1), (g - (-g)) x) :=
    volume_regionBetween_eq_integral ((hg_int_on (-(1/2)) (R - 1)).neg) (hg_int_on (-(1/2)) (R - 1))
      measurableSet_Ioc (fun x _ => by
        dsimp
        have h := hg_nonneg x
        linarith)
  have h_integrand_simp_g (x : ℝ) : (g - (-g)) x = 2 * g x := by
    simp [Pi.sub_apply, Pi.neg_apply, two_mul]
  have h_vol_right_to_Ioc : (volume S_right).toReal = (∫ x in Ioc (-(1/2)) (R - 1), 2 * g x) := by
    rw [h_vol_right_raw, ENNReal.toReal_ofReal (integral_nonneg (by
      intro x; rw [h_integrand_simp_g x]; positivity))]
    have h_fun_eq_g : (g - (-g)) = (fun x => 2 * g x) := by
      ext x; rw [h_integrand_simp_g x]
    rw [h_fun_eq_g]
  have h_vol_right : (volume S_right).toReal = (∫ x in (1/2 : ℝ)..R, 2 * f x) := by
    rw [h_vol_right_to_Ioc, ← intervalIntegral.integral_of_le (by linarith : (-(1/2 : ℝ)) ≤ R - 1)]
    calc
      (∫ x in (-(1/2 : ℝ))..(R - 1), 2 * g x) = (∫ x in (-(1/2 : ℝ))..(R - 1), 2 * f (x + 1)) := by
        refine intervalIntegral.integral_congr (fun x hx => ?_)
        unfold g f; simp
      _ = (∫ x in (-(1/2 : ℝ)) + 1..(R - 1) + 1, 2 * f x) := by
        rw [intervalIntegral.integral_comp_add_right (d := 1) (f := fun x => 2 * f x)]
      _ = (∫ x in (1/2 : ℝ)..R, 2 * f x) := by ring_nf
  -- FTC: compute the two integrals using the antiderivative F
  have h_deriv : ∀ x ∈ Ioo (-R) R, HasDerivAt F (2 * f x) x := by
    intro x hx
    have := hasDerivAt_intersect_antideriv R x hRpos hx
    simpa [F, f] using this
  have h_deriv_left : ∀ x ∈ Ioo (-R) (-(1/2)), HasDerivAt F (2 * f x) x := by
    intro x hx; apply h_deriv x; rcases hx with ⟨hl, hr⟩; exact ⟨hl, lt_trans hr (by linarith)⟩
  have h_deriv_right : ∀ x ∈ Ioo (1/2) R, HasDerivAt F (2 * f x) x := by
    intro x hx; apply h_deriv x; rcases hx with ⟨hl, hr⟩; exact ⟨lt_trans (by linarith) hl, hr⟩
  have h_int_left_FTC : (∫ x in (-R : ℝ)..(-(1/2)), 2 * f x) = F (-(1/2)) - F (-R) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith) (hF_cont.continuousOn) h_deriv_left
      ((hf_cont.const_mul 2).intervalIntegrable _ _)
  have h_int_right_FTC : (∫ x in (1/2 : ℝ)..R, 2 * f x) = F R - F (1/2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith) (hF_cont.continuousOn) h_deriv_right
      ((hf_cont.const_mul 2).intervalIntegrable _ _)
  -- Combine everything
  have h_total : (volume L).toReal =
      (F (-(1/2)) - F (-R)) + (F R - F (1/2)) := by
    rw [h_vol_eq, h_vol_union]
    have h_fin_left : volume S_left ≠ ∞ := by
      rw [h_vol_left_raw]; exact ENNReal.ofReal_ne_top
    have h_fin_right : volume S_right ≠ ∞ := by
      rw [h_vol_right_raw]; exact ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_add h_fin_left h_fin_right, h_vol_left, h_vol_right,
      h_int_left_FTC, h_int_right_FTC]
  calc
    (volume {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ R ^ 2 ∧ (p.1 + 1) ^ 2 + p.2 ^ 2 ≤ R ^ 2}).toReal
        = (volume L).toReal := by rw [← hL_def]
    _ = 2 * R ^ 2 * Real.arccos (1 / (2 * R)) - (1 / 2) * Real.sqrt (4 * R ^ 2 - 1) := by
      rw [h_total, hF_def]
      exact antideriv_lens_eq_aR R hR

/-- **Disc overlap ratio.** For two radius-R discs in ℂ whose centers are unit distance
    apart, the area of their intersection equals `πR²·ρ(R) = a(R)`.

    Proof: rotate u to 1, transfer to ℝ×ℝ via `measurableEquivRealProd`,
    then apply `lens_volume_eq_aR` and `Real.arccos_eq_pi_div_two_sub_arcsin` for the ρ-factor. -/
lemma disc_overlap_ratio_real (R : ℝ) (hR : R > 1/2) (u : ℂ) (hu : ‖u‖ = 1) :
    (volume {z : ℂ | ‖z‖ ≤ R ∧ ‖z + u‖ ≤ R}).toReal = (π * R ^ 2) * rho R := by
  have hRpos : R > 0 := by linarith
  -- Reduce RHS: (π*R²) * rho(R) = a(R) = 2R²·arccos(1/(2R)) − ½·√(4R²−1)
  have ha_formula : (2 * R ^ 2 * Real.arccos (1 / (2 * R)) - (1 / 2) * Real.sqrt (4 * R ^ 2 - 1)) =
      (π * R ^ 2) * rho R := by
    unfold rho
    split_ifs with hR'
    · field_simp [hRpos.ne.symm]
    · linarith
  rw [← ha_formula]
  -- Now goal: volume.toReal = 2R²·arccos(1/(2R)) − ½·√(4R²−1) = a(R)
  -- Step 1: rotate u → 1 via multiplication by u⁻¹ (isometry since |u|=1)
  have hu_ne : u ≠ 0 := by
    intro hzero; rw [hzero, norm_zero] at hu; linarith
  have h_norm_inv : ‖u⁻¹‖ = 1 := by
    rw [norm_inv, hu, inv_one]
  let φ : ℂ ≃ₗᵢ[ℝ] ℂ :=
    { toFun := fun z => u⁻¹ * z
      invFun := fun z => u * z
      map_add' := fun x y => mul_add _ _ _
      map_smul' := fun r z => by
        dsimp
        calc
          u⁻¹ * (r • z) = u⁻¹ * ((algebraMap ℝ ℂ) r * z) := by rw [Algebra.smul_def]
          _ = (algebraMap ℝ ℂ) r * (u⁻¹ * z) := by ring
          _ = r • (u⁻¹ * z) := by rw [Algebra.smul_def]
      left_inv := fun z => by field_simp [hu_ne]
      right_inv := fun z => by field_simp [hu_ne]
      norm_map' := fun z => by
        dsimp
        rw [norm_mul, h_norm_inv, one_mul] }
  have hφ_meas : MeasurePreserving (φ : ℂ → ℂ) := LinearIsometryEquiv.measurePreserving φ
  have hφ_emb : MeasurableEmbedding (φ : ℂ → ℂ) :=
    φ.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hφ_preimage : φ ⁻¹' {z | ‖z‖ ≤ R ∧ ‖z + 1‖ ≤ R} = {z | ‖z‖ ≤ R ∧ ‖z + u‖ ≤ R} := by
    ext z
    constructor
    · intro h; rcases h with ⟨hnorm, hsum⟩
      dsimp [φ] at hnorm hsum
      rw [norm_mul, h_norm_inv, one_mul] at hnorm
      have h2 : ‖z + u‖ ≤ R := by
        calc
          ‖z + u‖ = ‖u⁻¹ * (z + u)‖ := by
            rw [norm_mul, h_norm_inv, one_mul]
          _ = ‖u⁻¹ * z + u⁻¹ * u‖ := by ring_nf
          _ = ‖u⁻¹ * z + 1‖ := by field_simp [hu_ne]
          _ ≤ R := hsum
      exact ⟨hnorm, h2⟩
    · intro h; rcases h with ⟨hnorm, hsum⟩
      dsimp [φ]
      have h1 : ‖u⁻¹ * z‖ ≤ R := by rw [norm_mul, h_norm_inv, one_mul]; exact hnorm
      have h2 : ‖u⁻¹ * z + 1‖ ≤ R := by
        calc
          ‖u⁻¹ * z + 1‖ = ‖u⁻¹ * z + u⁻¹ * u‖ := by field_simp [hu_ne]
          _ = ‖u⁻¹ * (z + u)‖ := by ring_nf
          _ = ‖z + u‖ := by rw [norm_mul, h_norm_inv, one_mul]
          _ ≤ R := hsum
      exact ⟨h1, h2⟩
  have h_vol_rot : volume {z : ℂ | ‖z‖ ≤ R ∧ ‖z + u‖ ≤ R} =
      volume {z : ℂ | ‖z‖ ≤ R ∧ ‖z + 1‖ ≤ R} := by
    calc
      volume {z : ℂ | ‖z‖ ≤ R ∧ ‖z + u‖ ≤ R}
          = volume (φ ⁻¹' {z | ‖z‖ ≤ R ∧ ‖z + 1‖ ≤ R}) := by rw [← hφ_preimage]
      _ = volume {z : ℂ | ‖z‖ ≤ R ∧ ‖z + 1‖ ≤ R} :=
        hφ_meas.measure_preimage_emb hφ_emb _
  rw [h_vol_rot]
  -- Step 2: transfer ℂ → ℝ×ℝ via `measurableEquivRealProd`
  let e : ℂ ≃ᵐ ℝ × ℝ := Complex.measurableEquivRealProd
  have he_pres : MeasurePreserving (e : ℂ → ℝ × ℝ) := Complex.volume_preserving_equiv_real_prod
  have he_preimage : e ⁻¹' {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ R ^ 2 ∧ (p.1 + 1) ^ 2 + p.2 ^ 2 ≤ R ^ 2}
      = {z : ℂ | ‖z‖ ≤ R ∧ ‖z + 1‖ ≤ R} := by
    have hRnn : 0 ≤ R := by linarith
    have h_norm_iff (z : ℂ) : ‖z‖ ≤ R ↔ z.re ^ 2 + z.im ^ 2 ≤ R ^ 2 := by
      have hRnn : 0 ≤ R := by linarith
      have h_sq_eq : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
        calc
          z.re ^ 2 + z.im ^ 2 = Complex.normSq z := by
            simp [Complex.normSq_apply, sq]
          _ = ‖z‖ ^ 2 := by rw [Complex.normSq_eq_norm_sq]
      rw [h_sq_eq]
      have h_nn : 0 ≤ ‖z‖ := norm_nonneg _
      constructor
      · intro h; nlinarith
      · intro h; nlinarith
    have h_norm_add_iff (z : ℂ) : ‖z + 1‖ ≤ R ↔ (z.re + 1) ^ 2 + z.im ^ 2 ≤ R ^ 2 := by
      simpa [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im] using h_norm_iff (z + 1)
    ext z
    simp [e, Complex.measurableEquivRealProd_apply, h_norm_iff z, h_norm_add_iff z]
  have h_vol_re : volume {z : ℂ | ‖z‖ ≤ R ∧ ‖z + 1‖ ≤ R}
      = volume {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ R ^ 2 ∧ (p.1 + 1) ^ 2 + p.2 ^ 2 ≤ R ^ 2} := by
    calc
      volume {z : ℂ | ‖z‖ ≤ R ∧ ‖z + 1‖ ≤ R}
          = volume (e ⁻¹' {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ R ^ 2 ∧ (p.1 + 1) ^ 2 + p.2 ^ 2 ≤ R ^ 2}) := by
        rw [he_preimage]
      _ = volume {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ R ^ 2 ∧ (p.1 + 1) ^ 2 + p.2 ^ 2 ≤ R ^ 2} :=
        he_pres.measure_preimage_equiv _
  rw [h_vol_re]
  -- Step 3: apply the calculus lemma
  rw [lens_volume_eq_aR R hR]

/-- **Polydisc overlap ratio.** For unit vector u, vol(B_R ∩ B_R−u) = vol(B_R)·ρ(R)^f.
    Follows from disc_overlap_ratio_real and Fubini for the product measure. -/
lemma polydisc_overlap_ratio_real (f : ℕ) (R : ℝ) (hR : R > 1/2) (u : Fin f → ℂ)
    (hu : ∀ r : Fin f, ‖u r‖ = 1) :
    (volume (polydisc f R ∩ {x | x + u ∈ polydisc f R})).toReal =
    (volume (polydisc f R)).toReal * (rho R) ^ (f : ℕ) := by
  have hRnn : 0 ≤ R := by linarith
  -- Step 1: Rewrite polydisc and intersection as pi sets
  have hpoly_pi : polydisc f R =
      Set.pi Set.univ (fun _ : Fin f => Metric.closedBall (0 : ℂ) R) := by
    ext x; simp [polydisc, Set.mem_pi, Metric.mem_closedBall, dist_zero_right]
  have hint_pi : polydisc f R ∩ {x | x + u ∈ polydisc f R} =
      Set.pi Set.univ (fun r : Fin f => {z : ℂ | ‖z‖ ≤ R ∧ ‖z + u r‖ ≤ R}) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, polydisc, Set.mem_pi, Set.mem_univ,
               true_implies, Pi.add_apply]
    constructor
    · intro ⟨h1, h2⟩ r; exact ⟨h1 r, h2 r⟩
    · intro h; exact ⟨fun r => (h r).1, fun r => (h r).2⟩
  rw [hint_pi, hpoly_pi]
  -- Step 2: Expand volumes via the product formula (volume_pi_pi)
  have h_int : volume (Set.pi Set.univ (fun r : Fin f =>
        {z : ℂ | ‖z‖ ≤ R ∧ ‖z + u r‖ ≤ R})) =
      ∏ r : Fin f, volume {z : ℂ | ‖z‖ ≤ R ∧ ‖z + u r‖ ≤ R} := volume_pi_pi _
  have h_poly : volume (Set.pi Set.univ (fun _ : Fin f =>
        Metric.closedBall (0 : ℂ) R)) =
      ∏ _ : Fin f, volume (Metric.closedBall (0 : ℂ) R) := volume_pi_pi _
  rw [h_int, h_poly, ENNReal.toReal_prod, ENNReal.toReal_prod]
  -- Step 3: per-coordinate intersection volume (from disc_overlap_ratio_real)
  have hint_r : ∀ r : Fin f,
      (volume {z : ℂ | ‖z‖ ≤ R ∧ ‖z + u r‖ ≤ R}).toReal = π * R ^ 2 * rho R :=
    fun r => disc_overlap_ratio_real R hR (u r) (hu r)
  -- Step 4: per-coordinate polydisc volume (from Complex.volume_closedBall)
  have hpoly_r : (volume (Metric.closedBall (0 : ℂ) R)).toReal = π * R ^ 2 := by
    simp only [Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
               ENNReal.coe_toReal, NNReal.coe_real_pi, ENNReal.toReal_ofReal hRnn]
    ring
  simp_rw [hint_r, hpoly_r]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [mul_pow]

