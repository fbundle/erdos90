import Mathlib
import Erdos90.Defs
import Erdos90.Arithmetic
import Erdos90.DiscGeometry

open Real Filter NumberField Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal Topology Complex intervalIntegral Pointwise

noncomputable section

/-!
# Lemma 2.4: Coset averaging

Given the norm-one set U with |U| ≥ exp(γf), a lattice Λ ⊂ ℂ^f with a finite-volume
fundamental domain F, and R > 1/2 with log ρ(R) > -γ/2, there exists a coset a+Λ
whose intersection with the polydisc B_R has many ordered U-pairs.
-/

/-- **Lemma 2.4 (coset averaging).**  Given the norm-one set U with |U| ≥ exp(γf),
    a lattice Λ ⊂ ℂ^f (discrete, with fundamental domain F of finite covolume),
    and R > 1/2 with log ρ(R) > -γ/2, there exists a coset a+Λ whose intersection
    X with the polydisc B_R satisfies E ≥ exp(γf/2)·|X|, where E counts ordered
    pairs (x,y) ∈ X² with y−x ∈ U.

    Proof: average N(a) = |(a+Λ)∩B_R| and E(a) = Σ_{u∈U}|(a+Λ)∩B_R∩(B_R−u)|
    over the fundamental domain.  By the unfolding trick (lintegral_eq_tsum on F),
      ∫_F N(a) da = vol(B_R),   ∫_F E(a) da = Σ_u vol(B_R ∩ B_R−u).
    From polydisc_overlap_ratio_real and |U| ≥ exp(γf),
      ∫_F E ≥ exp(γf/2) · ∫_F N.
    By the averaging principle, some coset a achieves
      E(a) ≥ exp(γf/2) · N(a)  with N(a) > 0.
    Set X = (a+Λ) ∩ B_R to get the CosetAvgWitness. -/
def lemma_2_4 (f : ℕ) (hf1 : f ≥ 1) (Λ : AddSubgroup (Fin f → ℂ))
    (hΛ_countable : Countable Λ) (F : Set (Fin f → ℂ))
    (hF_fund : IsAddFundamentalDomain Λ F volume) (_hF_fin : volume F < ∞)
    (δ : ℝ) (hδ_pos : δ > 0) (hΛ_sep : ∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf1)‖ ≥ δ)
    (U : Finset (Fin f → ℂ))
    (hU_norm : ∀ u ∈ U, ∀ r : Fin f, ‖u r‖ = 1)
    (hU_in_Λ : ∀ u ∈ U, (u : Fin f → ℂ) ∈ Λ.carrier)
    (γ : ℝ) (_hγ : γ > 0)
    (hU_size : (U.card : ℝ) ≥ Real.exp (γ * (f : ℝ)))
    (R : ℝ) (hR : R > 1/2)
    (hρ : Real.log (rho R) > - (γ / 2)) :
    CosetAvgWitness f Λ U R γ := by
  -- Step 0: ρ(R) > 0 for R > 1/2 (positivity of disc overlap)
  have hrho_pos : rho R > 0 := by
    unfold rho
    split_ifs with h
    · have ha_pos : 2 * R ^ 2 * Real.arccos (1 / (2 * R)) - (1/2) * Real.sqrt (4 * R ^ 2 - 1) > 0 := a_pos R hR
      have den_pos : π * R ^ 2 > 0 := by positivity
      exact div_pos ha_pos den_pos
    · linarith
  -- Step 1: Algebraic inequality: |U| · ρ(R)^f ≥ exp(γf/2)
  have h_ineq : Real.exp (γ * (f : ℝ)) * (rho R) ^ (f : ℕ) ≥ Real.exp (γ / 2 * (f : ℝ)) := by
    have h_rho_pow : (rho R) ^ (f : ℕ) ≥ Real.exp (-(γ / 2 * (f : ℝ))) := by
      have h_rho_gt : rho R > Real.exp (-(γ / 2)) := by
        have := Real.exp_lt_exp.mpr hρ
        rw [Real.exp_log hrho_pos] at this
        exact this
      have h_pow_ge : (rho R) ^ (f : ℕ) ≥ (Real.exp (-(γ / 2))) ^ (f : ℕ) :=
        pow_le_pow_left₀ (Real.exp_nonneg _) h_rho_gt.le (f : ℕ)
      have h_exp_pow : (Real.exp (-(γ / 2))) ^ (f : ℕ) = Real.exp (-(γ / 2 * (f : ℝ))) := by
        calc
          (Real.exp (-(γ / 2))) ^ (f : ℕ) = Real.exp ((f : ℕ) * (-(γ / 2))) := by
            rw [← Real.exp_nat_mul]
          _ = Real.exp ((f : ℝ) * (-(γ / 2))) := by norm_cast
          _ = Real.exp (-(γ / 2 * (f : ℝ))) := by ring_nf
      rw [h_exp_pow] at h_pow_ge
      exact h_pow_ge
    calc
      Real.exp (γ * (f : ℝ)) * (rho R) ^ (f : ℕ)
          ≥ Real.exp (γ * (f : ℝ)) * Real.exp (-(γ / 2 * (f : ℝ))) := by gcongr
      _ = Real.exp ((γ * (f : ℝ)) + (-(γ / 2 * (f : ℝ)))) := by rw [← Real.exp_add]
      _ = Real.exp (γ / 2 * (f : ℝ)) := by ring_nf

  -- Step 2: Use the fundamental domain to find a good coset.
  let B_R : Set (Fin f → ℂ) := polydisc f R
  have hB_meas : MeasurableSet B_R := polydisc_measurable f R
  -- Finiteness of polydisc volume via compactness
  have hB_fin : volume B_R < ∞ := by
    have h_compact : IsCompact (polydisc f R) := by
      have h_pi : polydisc f R = Set.pi Set.univ (fun (_ : Fin f) => Metric.closedBall (0 : ℂ) R) := by
        ext z; simp [polydisc, Metric.mem_closedBall, dist_eq_norm]
      rw [h_pi]
      exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
    exact h_compact.measure_lt_top

  -- Algebraic estimate (done before measure-theoretic part):
  have h_overlap_sum : (∑ u ∈ U, (volume (B_R ∩ {x | x + u ∈ B_R})).toReal) ≥
      Real.exp (γ / 2 * (f : ℝ)) * (volume B_R).toReal := by
    have h_overlap_vol (u : Fin f → ℂ) (hu : u ∈ U) :
        (volume (B_R ∩ {x | x + u ∈ B_R})).toReal = (volume B_R).toReal * (rho R) ^ (f : ℕ) :=
      polydisc_overlap_ratio_real f R hR u (hU_norm u hu)
    have h_card_rho : (U.card : ℝ) * (rho R) ^ (f : ℕ) ≥ Real.exp (γ / 2 * (f : ℝ)) := by
      have h1 : (U.card : ℝ) * (rho R) ^ (f : ℕ) ≥ Real.exp (γ * (f : ℝ)) * (rho R) ^ (f : ℕ) := by
        have hpos : 0 ≤ (rho R) ^ (f : ℕ) := pow_nonneg (by linarith) _
        exact mul_le_mul_of_nonneg_right hU_size hpos
      linarith [h_ineq]
    calc
      (∑ u ∈ U, (volume (B_R ∩ {x | x + u ∈ B_R})).toReal)
          = (∑ u ∈ U, (volume B_R).toReal * (rho R) ^ (f : ℕ)) :=
            Finset.sum_congr rfl fun u hu => by rw [h_overlap_vol u hu]
      _ = (U.card : ℝ) * ((volume B_R).toReal * (rho R) ^ (f : ℕ)) := by simp
      _ = ((U.card : ℝ) * (rho R) ^ (f : ℕ)) * (volume B_R).toReal := by ring
      _ ≥ Real.exp (γ / 2 * (f : ℝ)) * (volume B_R).toReal := by gcongr

  -- The coset averaging argument using the fundamental domain hF_fund.
  -- Key identity (unfolding): vol(S) = ∑'_{g∈Λ} vol({a∈F | a+g ∈ S}) for measurable S.
  -- This follows from hF_fund.measure_eq_tsum + translation invariance.
  have h_unfold_vol (S : Set (Fin f → ℂ)) (hS_meas : MeasurableSet S) :
      volume S = ∑' (g : Λ), volume (F ∩ {x | x + (g : Fin f → ℂ) ∈ S}) := by
    have h_meas_eq := hF_fund.measure_eq_tsum' S
    -- h_meas_eq: volume S = ∑' (g : Λ), volume (S ∩ ((g : Λ) +ᵥ F))
    rw [h_meas_eq]
    refine tsum_congr (fun g => ?_)
    -- Need: volume (S ∩ ((g : Λ) +ᵥ F)) = volume (F ∩ {x | x + (g : Fin f → ℂ) ∈ S})
    -- Use translation invariance: the map φ(x) = g + x is measure-preserving.
    let φ := fun x : Fin f → ℂ => (g : Fin f → ℂ) + x
    have h_φ_meas_pres : map φ volume = volume :=
      IsAddLeftInvariant.map_add_left_eq_self (g : Fin f → ℂ)
    -- φ⁻¹'(S) = {x | x + g ∈ S} and φ⁻¹'((g:Λ)+ᵥF) = F
    have h_pre_S : φ ⁻¹' S = {x | x + (g : Fin f → ℂ) ∈ S} := by
      ext x; simp [φ, add_comm]
    have h_pre_vadd : φ ⁻¹' ((g : Λ) +ᵥ F) = F := by
      ext x; constructor
      · intro h
        have hmem : φ x ∈ (g : Λ) +ᵥ F := h
        rcases Set.mem_vadd_set.1 hmem with ⟨y, hyF, hy_eq⟩
        have hφ : φ x = (g : Fin f → ℂ) + x := rfl
        rw [hφ] at hy_eq
        -- hy_eq: (g : Λ) +ᵥ y = (g : Fin f → ℂ) + x
        -- Since VAdd for AddSubgroup is g +ᵥ y = g.val + y, we get g + y = g + x, so y = x
        have h_vadd : (g : Λ) +ᵥ y = (g : Fin f → ℂ) + y := rfl
        rw [h_vadd] at hy_eq
        have hy_eq_x : y = x := add_left_cancel hy_eq
        rw [← hy_eq_x]
        exact hyF
      · intro hx
        rw [Set.mem_preimage]
        have hφ : φ x = (g : Fin f → ℂ) + x := rfl
        rw [hφ]
        exact Set.mem_vadd_set.mpr ⟨x, hx, rfl⟩
    have h_pre_inter : φ ⁻¹' (S ∩ ((g : Λ) +ᵥ F))
        = (F ∩ {x | x + (g : Fin f → ℂ) ∈ S}) := by
      rw [Set.preimage_inter, h_pre_S, h_pre_vadd, Set.inter_comm]
    have h_nmeas_vadd : NullMeasurableSet ((g : Λ) +ᵥ F) volume :=
      hF_fund.nullMeasurableSet.vadd (g : Λ)
    calc
      volume (S ∩ ((g : Λ) +ᵥ F))
          = volume (φ ⁻¹' (S ∩ ((g : Λ) +ᵥ F))) :=
        (measure_preimage_of_map_eq_self h_φ_meas_pres
          ((hS_meas.nullMeasurableSet).inter h_nmeas_vadd)).symm
      _ = volume (F ∩ {x | x + (g : Fin f → ℂ) ∈ S}) := by rw [h_pre_inter]

  -- Using h_unfold_vol, we get the integral identities by swapping sum and integral.
  -- Define indicator function
  let ind (S : Set (Fin f → ℂ)) (x : Fin f → ℂ) : ℝ≥0∞ := S.indicator (fun _ => (1 : ℝ≥0∞)) x

  have h_unfold (S : Set (Fin f → ℂ)) (hS_meas : MeasurableSet S) :
      ∫⁻ a in F, (∑' (g : Λ), ind S (a + (g : Fin f → ℂ))) ∂volume = volume S := by
    have h_swap : ∫⁻ a in F, (∑' (g : Λ), ind S (a + (g : Fin f → ℂ))) ∂volume
        = ∑' (g : Λ), ∫⁻ a in F, ind S (a + (g : Fin f → ℂ)) ∂volume := by
      calc
        ∫⁻ a in F, (∑' (g : Λ), ind S (a + (g : Fin f → ℂ))) ∂volume
            = ∫⁻ a, (∑' (g : Λ), ind S (a + (g : Fin f → ℂ))) ∂(volume.restrict F) := rfl
        _ = ∑' (g : Λ), ∫⁻ a, ind S (a + (g : Fin f → ℂ)) ∂(volume.restrict F) :=
          lintegral_tsum (fun g => by
            have h_meas_add : Measurable (fun a : Fin f → ℂ => a + (g : Fin f → ℂ)) :=
              measurable_add_const (g : Fin f → ℂ)
            have h_meas : Measurable (S.indicator (fun _ : Fin f → ℂ => (1 : ℝ≥0∞))) :=
              (measurable_const : Measurable (fun _ : Fin f → ℂ => (1 : ℝ≥0∞))).indicator hS_meas
            exact (h_meas.comp h_meas_add).aemeasurable)
        _ = ∑' (g : Λ), ∫⁻ a in F, ind S (a + (g : Fin f → ℂ)) ∂volume := rfl
    have h_inner (g : Λ) : ∫⁻ a in F, ind S (a + (g : Fin f → ℂ)) ∂volume
        = volume (F ∩ {x | x + (g : Fin f → ℂ) ∈ S}) := by
      let T := {x | x + (g : Fin f → ℂ) ∈ S}
      have hT_meas : MeasurableSet T := hS_meas.preimage (measurable_add_const (g : Fin f → ℂ))
      have h_eq : (fun a => ind S (a + (g : Fin f → ℂ))) = T.indicator (fun _ => (1 : ℝ≥0∞)) := by
        refine funext (fun a => ?_)
        dsimp [ind, T]
        classical
        simp [Set.indicator_apply, Set.mem_setOf_eq]
      rw [h_eq]
      rw [setLIntegral_indicator hT_meas (fun _ => (1 : ℝ≥0∞)), setLIntegral_one, Set.inter_comm]
    rw [h_swap]
    simp_rw [h_inner]
    exact (h_unfold_vol S hS_meas).symm

  -- Apply unfolding to B_R (N integral) and to overlap sets (E_u integrals)
  have h_int_N : ∫⁻ a in F, (∑' (g : Λ), ind B_R (a + (g : Fin f → ℂ))) ∂volume = volume B_R :=
    h_unfold B_R hB_meas

  let S_u (u : Fin f → ℂ) : Set (Fin f → ℂ) := B_R ∩ {x | x + u ∈ B_R}
  have hS_meas (u : Fin f → ℂ) (hu : u ∈ U) : MeasurableSet (S_u u) :=
    hB_meas.inter (hB_meas.preimage (measurable_add_const u))
  have h_int_Eu (u : Fin f → ℂ) (hu : u ∈ U) :
      ∫⁻ a in F, (∑' (g : Λ), ind (S_u u) (a + (g : Fin f → ℂ))) ∂volume = volume (S_u u) :=
    h_unfold (S_u u) (hS_meas u hu)

  -- Now the averaging: from h_overlap_sum, we have in ℝ:
  --   ∑_u vol(S_u).toReal ≥ exp(γf/2) * vol(B_R).toReal
  -- Convert to ENNReal inequality using finiteness of volumes.
  have h_int_ineq : (∑ u ∈ U, ∫⁻ a in F, (∑' (g : Λ), ind (S_u u) (a + (g : Fin f → ℂ))) ∂volume) ≥
      ENNReal.ofReal (Real.exp (γ / 2 * (f : ℝ))) *
      ∫⁻ a in F, (∑' (g : Λ), ind B_R (a + (g : Fin f → ℂ))) ∂volume := by
    -- Need: (∑ u ∈ U, volume (S_u u)) ≥ ENNReal.ofReal (Real.exp (γ / 2 * (f : ℝ))) * volume B_R
    -- This follows from h_overlap_sum by converting .toReal back to ENNReal
    -- Step 1: rewrite integrals to volumes
    rw [show (∑ u ∈ U, ∫⁻ a in F, (∑' (g : Λ), ind (S_u u) (a + (g : Fin f → ℂ))) ∂volume) =
        ∑ u ∈ U, volume (S_u u) from
      Finset.sum_congr rfl (fun u hu => h_int_Eu u hu)]
    rw [h_int_N]
    -- Step 2: finiteness facts
    have hS_fin : ∀ u ∈ U, volume (S_u u) < ∞ := fun u _ => by
      apply lt_of_le_of_lt (measure_mono Set.inter_subset_left)
      exact hB_fin
    have hS_ne_top : ∀ u ∈ U, volume (S_u u) ≠ ∞ := fun u hu =>
      (hS_fin u hu).ne
    have hSum_ne_top : (∑ u ∈ U, volume (S_u u)) ≠ ∞ :=
      (ENNReal.sum_lt_top.mpr hS_fin).ne
    have hB_ne_top : volume B_R ≠ ∞ := hB_fin.ne
    have hMul_ne_top : ENNReal.ofReal (Real.exp (γ / 2 * (f : ℝ))) * volume B_R ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB_ne_top
    -- Step 3: convert ENNReal ≥ to Real ≥ via toReal
    rw [ge_iff_le, ← ENNReal.toReal_le_toReal hMul_ne_top hSum_ne_top]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    rw [ENNReal.toReal_sum hS_ne_top]
    -- Step 4: use h_overlap_sum (which is about S_u u = B_R ∩ {x | x + u ∈ B_R})
    exact h_overlap_sum

  -- Define the pointwise functions on F:
  --   N_fun a = ∑'_{g ∈ Λ} ind B_R (a + g)     (counts lattice pts of coset a+Λ in B_R)
  --   E_fun a = ∑_{u ∈ U} ∑'_{g ∈ Λ} ind (S_u u) (a + g)  (pair count)
  let N_fun : (Fin f → ℂ) → ℝ≥0∞ :=
    fun a => ∑' (g : Λ), ind B_R (a + (g : Fin f → ℂ))
  let E_fun : (Fin f → ℂ) → ℝ≥0∞ :=
    fun a => ∑ u ∈ U, ∑' (g : Λ), ind (S_u u) (a + (g : Fin f → ℂ))
  -- The integral inequality h_int_ineq says:
  --   ∫_F E_fun ≥ c * ∫_F N_fun   where c = exp(γ/2*f)
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ / 2 * (f : ℝ)))
  have h_E_integral : ∫⁻ a in F, E_fun a ∂volume =
      ∑ u ∈ U, ∫⁻ a in F, ∑' (g : Λ), ind (S_u u) (a + (g : Fin f → ℂ)) ∂volume := by
    simp only [E_fun]
    rw [← lintegral_finset_sum]
    intro u hu
    apply Measurable.ennreal_tsum
    intro g
    have h_meas_add : Measurable (fun a : Fin f → ℂ => a + (g : Fin f → ℂ)) :=
      measurable_add_const (g : Fin f → ℂ)
    have h_meas : Measurable ((S_u u).indicator (fun _ : Fin f → ℂ => (1 : ℝ≥0∞))) :=
      (measurable_const : Measurable (fun _ : Fin f → ℂ => (1 : ℝ≥0∞))).indicator (hS_meas u hu)
    exact h_meas.comp h_meas_add
  have h_int_ineq' : ∫⁻ a in F, E_fun a ∂volume ≥ c * ∫⁻ a in F, N_fun a ∂volume := by
    rw [h_E_integral]
    exact h_int_ineq
  -- The volume of B_R is positive (open interior is nonempty, contains 0)
  have hB_pos : 0 < volume B_R := by
    -- The open strict polydisc {z | ∀ r, ‖z r‖ < R} is open, nonempty, and ⊆ B_R
    have hR_pos : R > 0 := by linarith
    have h_open_poly : IsOpen {z : Fin f → ℂ | ∀ r : Fin f, ‖z r‖ < R} := by
      have heq : {z : Fin f → ℂ | ∀ r : Fin f, ‖z r‖ < R} =
          ⋂ r : Fin f, {z | ‖z r‖ < R} := by
        ext z; simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [heq]
      apply isOpen_iInter_of_finite
      intro r
      exact isOpen_lt (continuous_norm.comp (continuous_apply r)) continuous_const
    have h_ne : (0 : Fin f → ℂ) ∈ {z : Fin f → ℂ | ∀ r : Fin f, ‖z r‖ < R} := by
      intro r
      simp only [Pi.zero_apply, norm_zero]
      exact hR_pos
    have h_sub : {z : Fin f → ℂ | ∀ r : Fin f, ‖z r‖ < R} ⊆ B_R := by
      intro z hz; exact fun r => le_of_lt (hz r)
    calc 0 < volume {z : Fin f → ℂ | ∀ r : Fin f, ‖z r‖ < R} :=
          h_open_poly.measure_pos volume ⟨0, h_ne⟩
      _ ≤ volume B_R := measure_mono h_sub
  -- ∫_F N_fun > 0 follows from h_int_N and hB_pos
  have h_N_integral_pos : 0 < ∫⁻ a in F, N_fun a ∂volume := by
    rw [h_int_N]
    exact hB_pos
  -- ∫_F E_fun > 0 follows from h_int_ineq' and h_N_integral_pos
  have h_E_integral_pos : 0 < ∫⁻ a in F, E_fun a ∂volume := by
    have hc_pos : 0 < c := by
      simp only [c, ENNReal.ofReal_pos]
      exact Real.exp_pos _
    calc 0 < c * ∫⁻ a in F, N_fun a ∂volume := ENNReal.mul_pos hc_pos.ne' h_N_integral_pos.ne'
      _ ≤ ∫⁻ a in F, E_fun a ∂volume := h_int_ineq'
  -- PART A: Exact formula ∫_F E_fun = |U| · ρ^f · vol(B_R)
  -- Each h_int_Eu gives vol(S_u u) = vol(B_R) · ρ^f (via polydisc_overlap_ratio_real),
  -- so ∫_F E_fun = ∑_u vol(S_u u) = U.card · vol(B_R) · ρ^f = U.card · ρ^f · vol(B_R).
  let c' : ℝ≥0∞ := U.card * ENNReal.ofReal ((rho R) ^ (f : ℕ))
  have h_E_exact : ∫⁻ a in F, E_fun a ∂volume = c' * volume B_R := by
    calc
      ∫⁻ a in F, E_fun a ∂volume
          = ∑ u ∈ U, ∫⁻ a in F, ∑' (g : Λ), ind (S_u u) (a + (g : Fin f → ℂ)) ∂volume := h_E_integral
      _ = ∑ u ∈ U, volume (S_u u) := by
        refine Finset.sum_congr rfl (fun u hu => ?_)
        rw [h_int_Eu u hu]
      _ = ∑ u ∈ U, (volume B_R * ENNReal.ofReal ((rho R) ^ (f : ℕ))) := by
        refine Finset.sum_congr rfl (fun u hu => ?_)
        have h_vol_eq : volume (S_u u) = volume B_R * ENNReal.ofReal ((rho R) ^ (f : ℕ)) := by
          have hvol_real : (volume (S_u u)).toReal = (volume B_R).toReal * (rho R) ^ (f : ℕ) :=
            polydisc_overlap_ratio_real f R hR u (hU_norm u hu)
          have hfin_S : volume (S_u u) < ∞ := by
            apply lt_of_le_of_lt (measure_mono Set.inter_subset_left)
            exact hB_fin
          calc
            volume (S_u u) = ENNReal.ofReal ((volume (S_u u)).toReal) :=
              (ENNReal.ofReal_toReal hfin_S.ne).symm
            _ = ENNReal.ofReal ((volume B_R).toReal * (rho R) ^ (f : ℕ)) := by rw [hvol_real]
            _ = ENNReal.ofReal ((volume B_R).toReal) * ENNReal.ofReal ((rho R) ^ (f : ℕ)) := by
              rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
            _ = volume B_R * ENNReal.ofReal ((rho R) ^ (f : ℕ)) := by
              rw [ENNReal.ofReal_toReal hB_fin.ne]
        exact h_vol_eq
      _ = (U.card : ℝ≥0∞) * (volume B_R * ENNReal.ofReal ((rho R) ^ (f : ℕ))) := by
        simp
      _ = U.card * ENNReal.ofReal ((rho R) ^ (f : ℕ)) * volume B_R := by ring
      _ = c' * volume B_R := rfl
  -- By the averaging principle: ∃ a₀ ∈ F with E_fun(a₀) ≥ c * N_fun(a₀) and N_fun(a₀) ≠ 0.
  -- Strategy: the exact formula ∫_F E_fun = c' · vol(B_R) = c' · ∫_F N_fun,
  -- combined with h_int_ineq' (∫_F E_fun ≥ c · ∫_F N_fun), shows that
  -- E_fun ≥ c · N_fun cannot fail on a set of full measure.  A set where it fails
  -- would decrease the integral strictly, giving ∫_F E_fun < c' · ∫_F N_fun = ∫_F E_fun — contradiction.
  -- Since we are in a def (Type-valued), we use Classical.choice to extract witnesses.
  have h_avg_exists : ∃ a₀ ∈ F, N_fun a₀ ≠ 0 ∧ E_fun a₀ ≥ c * N_fun a₀ := by
    have hN_meas : Measurable N_fun := by
      dsimp [N_fun]
      refine Measurable.ennreal_tsum fun (g : Λ) => ?_
      have h_meas_ind : Measurable (ind B_R) :=
        (measurable_const : Measurable (fun _ : Fin f → ℂ => (1 : ℝ≥0∞))).indicator hB_meas
      exact h_meas_ind.comp (measurable_add_const (g : Fin f → ℂ))
    have hE_int_fin : ∫⁻ a in F, E_fun a ∂volume ≠ ∞ := by
      rw [h_E_exact]
      have hc' : c' ≠ ∞ := by
        dsimp [c']
        exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
      exact ENNReal.mul_ne_top hc' hB_fin.ne
    have h_ind_le (S : Set (Fin f → ℂ)) (hS_sub : S ⊆ B_R) (x : Fin f → ℂ) :
        ind S x ≤ ind B_R x := by
      dsimp [ind]
      classical
      by_cases hxS : x ∈ S
      · have hxB : x ∈ B_R := hS_sub hxS
        simp [hxS, hxB]
      · by_cases hxB : x ∈ B_R
        · simp [hxS, hxB]
        · simp [hxS, hxB]
    have hE_le_card_N : ∀ a, E_fun a ≤ (U.card : ℝ≥0∞) * N_fun a := by
      intro a
      dsimp [E_fun, N_fun]
      calc
        ∑ u ∈ U, ∑' (g : Λ), ind (S_u u) (a + (g : Fin f → ℂ))
            ≤ ∑ u ∈ U, ∑' (g : Λ), ind B_R (a + (g : Fin f → ℂ)) := by
          refine Finset.sum_le_sum (fun u hu => ?_)
          refine ENNReal.tsum_le_tsum (fun g => h_ind_le (S_u u) (Set.inter_subset_left) _)
        _ = ∑ u ∈ U, N_fun a := rfl
        _ = (U.card : ℝ≥0∞) * N_fun a := by simp
    have hN_nonneg : ∀ a, 0 ≤ N_fun a := fun a =>
      tsum_nonneg (fun (g : Λ) => zero_le _)
    let s_pos : Set (Fin f → ℂ) := {a | 0 < N_fun a}
    by_contra h_no
    push Not at h_no
    have h_le_pt : ∀ a ∈ F, E_fun a ≤ c * N_fun a := by
      intro a ha
      have h_cases' : N_fun a = 0 ∨ ¬(E_fun a ≥ c * N_fun a) := by
        have h_no_a := h_no a ha
        -- h_no_a : N_fun a ≠ 0 → ¬(E_fun a ≥ c * N_fun a)
        by_cases hNzero : N_fun a = 0
        · left; exact hNzero
        · right; exact not_le.mpr (h_no_a hNzero)
      rcases h_cases' with (hNzero | h_not_ge)
      · have hEzero : E_fun a = 0 := by
          apply le_antisymm ?_ (zero_le _)
          calc
            E_fun a ≤ (U.card : ℝ≥0∞) * N_fun a := hE_le_card_N a
            _ = (U.card : ℝ≥0∞) * 0 := by rw [hNzero]
            _ = 0 := by simp
        rw [hEzero]
        simp [c]
      · have h_lt : E_fun a < c * N_fun a := lt_of_not_ge h_not_ge
        exact le_of_lt h_lt
    have h_ae_le : E_fun ≤ᵐ[volume.restrict F] (fun x => c * N_fun x) := by
      refine (ae_restrict_iff'₀ hF_fund.nullMeasurableSet).mpr ?_
      refine ae_of_all volume ?_
      intro a haF
      have := h_le_pt a haF
      simpa using this
    have h_int_le : ∫⁻ a in F, E_fun a ∂volume ≤ c * ∫⁻ a in F, N_fun a ∂volume := by
      calc
        ∫⁻ a in F, E_fun a ∂volume = ∫⁻ a, E_fun a ∂(volume.restrict F) := rfl
        _ ≤ ∫⁻ a, c * N_fun a ∂(volume.restrict F) := by
          -- h_ae_le : E_fun ≤ᵐ[μ] (fun x => c * N_fun x)
          -- lintegral_mono gives ∫ E ≤ ∫ (fun x => c * N_fun x)
          -- which is definitionally ∫ E ≤ ∫ c*N
          simpa using lintegral_mono_ae h_ae_le
        _ = c * ∫⁻ a, N_fun a ∂(volume.restrict F) := by rw [lintegral_const_mul c hN_meas]
        _ = c * ∫⁻ a in F, N_fun a ∂volume := rfl
    have h_int_eq : ∫⁻ a in F, E_fun a ∂volume = c * ∫⁻ a in F, N_fun a ∂volume :=
      le_antisymm h_int_le h_int_ineq'
    have hμs_pos : (volume.restrict F) s_pos ≠ 0 := by
      intro hzero
      have h_eq_set : {a | N_fun a ≠ 0} = s_pos := by
        ext a; simp [s_pos, hN_nonneg a]
      have hzero' : (volume.restrict F) {a | N_fun a ≠ 0} = 0 := by
        rw [h_eq_set, hzero]
      have h_ae_N_zero : N_fun =ᵐ[volume.restrict F] 0 :=
        ae_iff.mpr hzero'
      have h_int_N_zero : ∫⁻ a in F, N_fun a ∂volume = 0 := by
        calc
          ∫⁻ a in F, N_fun a ∂volume = ∫⁻ a, N_fun a ∂(volume.restrict F) := rfl
          _ = ∫⁻ a, 0 ∂(volume.restrict F) := lintegral_congr_ae h_ae_N_zero
          _ = 0 := by simp
      rw [h_int_N] at h_int_N_zero
      exact hB_pos.ne' h_int_N_zero
    have h_strict : ∀ᵐ a ∂(volume.restrict F), a ∈ s_pos → E_fun a < c * N_fun a := by
      refine (ae_restrict_iff'₀ hF_fund.nullMeasurableSet).mpr ?_
      apply ae_of_all volume
      intro a haF has_pos
      have h_cases' : N_fun a = 0 ∨ ¬(E_fun a ≥ c * N_fun a) := by
        have h_no_a := h_no a haF
        by_cases hNzero : N_fun a = 0
        · left; exact hNzero
        · right; exact not_le.mpr (h_no_a hNzero)
      rcases h_cases' with (hNzero | h_not_ge)
      · exact absurd hNzero has_pos.ne'
      · exact lt_of_not_ge h_not_ge
    have h_int_lt : ∫⁻ a in F, E_fun a ∂volume < c * ∫⁻ a in F, N_fun a ∂volume := by
      calc
        ∫⁻ a in F, E_fun a ∂volume = ∫⁻ a, E_fun a ∂(volume.restrict F) := rfl
        _ < ∫⁻ a, (c * N_fun a) ∂(volume.restrict F) :=
          lintegral_strict_mono_of_ae_le_of_ae_lt_on
            (hN_meas.const_mul c).aemeasurable hE_int_fin h_ae_le hμs_pos h_strict
        _ = c * ∫⁻ a, N_fun a ∂(volume.restrict F) := by rw [lintegral_const_mul c hN_meas]
        _ = c * ∫⁻ a in F, N_fun a ∂volume := rfl
    exact lt_irrefl _ (h_int_lt.trans_eq h_int_eq.symm)
  -- Unpack using Classical.choose (works in noncomputable def context)
  -- ∃ a₀ ∈ F, P desugars to ∃ a₀, a₀ ∈ F ∧ P in Lean 4
  let a₀ : Fin f → ℂ := h_avg_exists.choose
  have ha₀_F : a₀ ∈ F := h_avg_exists.choose_spec.1
  have hN_pos : N_fun a₀ ≠ 0 := h_avg_exists.choose_spec.2.1
  have hE_ge : E_fun a₀ ≥ c * N_fun a₀ := h_avg_exists.choose_spec.2.2
  let G : Set Λ := {g | a₀ + (g : Fin f → ℂ) ∈ B_R}
  have hG_fin : Set.Finite G := by
    let φ : Λ → ℂ := fun g => (g : Fin f → ℂ) (fin0 hf1)
    have hφ_inj : Function.Injective φ := by
      intro g₁ g₂ h
      apply Subtype.ext
      by_contra h_ne
      have h_nonzero : (g₁ : Fin f → ℂ) - (g₂ : Fin f → ℂ) ≠ 0 := sub_ne_zero.mpr h_ne
      have h_mem : (g₁ : Fin f → ℂ) - (g₂ : Fin f → ℂ) ∈ Λ :=
        Λ.sub_mem g₁.property g₂.property
      have h_sep := hΛ_sep ((g₁ : Fin f → ℂ) - (g₂ : Fin f → ℂ)) h_mem h_nonzero
      have h_diff_zero : ((g₁ : Fin f → ℂ) - (g₂ : Fin f → ℂ)) (fin0 hf1) = 0 := by
        calc
          ((g₁ : Fin f → ℂ) - (g₂ : Fin f → ℂ)) (fin0 hf1)
              = (g₁ : Fin f → ℂ) (fin0 hf1) - (g₂ : Fin f → ℂ) (fin0 hf1) := rfl
          _ = φ g₁ - φ g₂ := rfl
          _ = 0 := by rw [h, sub_self]
      rw [h_diff_zero, norm_zero] at h_sep
      linarith [hδ_pos]
    set M := R + ‖a₀ (fin0 hf1)‖ with hM_def
    have hZ_bounded : ∀ z ∈ φ '' G, ‖z‖ ≤ M := by
      intro z hz
      rcases hz with ⟨g, hg, rfl⟩
      have hB_f0 : ‖(a₀ + (g : Fin f → ℂ)) (fin0 hf1)‖ ≤ R := hg (fin0 hf1)
      calc
        ‖(g : Fin f → ℂ) (fin0 hf1)‖
            = ‖((a₀ + (g : Fin f → ℂ)) - a₀) (fin0 hf1)‖ := by simp
        _ ≤ ‖(a₀ + (g : Fin f → ℂ)) (fin0 hf1)‖ + ‖a₀ (fin0 hf1)‖ := norm_sub_le _ _
        _ ≤ R + ‖a₀ (fin0 hf1)‖ := by gcongr
        _ = M := rfl
    have hZ_sep : ∀ x y, x ∈ φ '' G → y ∈ φ '' G → x ≠ y → dist x y ≥ δ := by
      intro x y hx hy hne
      rcases hx with ⟨g₁, hg₁, rfl⟩
      rcases hy with ⟨g₂, hg₂, rfl⟩
      have hg_ne : g₁ ≠ g₂ := by
        intro h_eq; apply hne; rw [h_eq]
      have h_nonzero : (g₁ : Fin f → ℂ) - (g₂ : Fin f → ℂ) ≠ 0 := sub_ne_zero.mpr (Subtype.coe_injective.ne hg_ne)
      have h_mem : (g₁ : Fin f → ℂ) - (g₂ : Fin f → ℂ) ∈ Λ :=
        Λ.sub_mem g₁.property g₂.property
      have h_sep := hΛ_sep ((g₁ : Fin f → ℂ) - (g₂ : Fin f → ℂ)) h_mem h_nonzero
      calc
        dist ((g₁ : Fin f → ℂ) (fin0 hf1)) ((g₂ : Fin f → ℂ) (fin0 hf1))
            = ‖(g₁ : Fin f → ℂ) (fin0 hf1) - (g₂ : Fin f → ℂ) (fin0 hf1)‖ := dist_eq_norm _ _
        _ = ‖((g₁ : Fin f → ℂ) - (g₂ : Fin f → ℂ)) (fin0 hf1)‖ := rfl
        _ ≥ δ := h_sep
    have hZ_fin : Set.Finite (φ '' G) := by
      have h_compact : IsCompact (Metric.closedBall (0 : ℂ) M) := isCompact_closedBall _ _
      have h_sub : φ '' G ⊆ Metric.closedBall (0 : ℂ) M := by
        intro z hz
        rcases hz with ⟨g, hg, rfl⟩
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        exact hZ_bounded ((g : Fin f → ℂ) (fin0 hf1)) ⟨g, hg, rfl⟩
      by_contra h_inf
      have h_infinite : Set.Infinite (φ '' G) := Set.not_finite.mp h_inf
      have h_tb : TotallyBounded (Metric.closedBall (0 : ℂ) M) :=
        IsCompact.totallyBounded h_compact
      rcases Metric.totallyBounded_iff.mp h_tb (δ/2) (by linarith [hδ_pos]) with ⟨C, hC_fin, h_cover⟩
      -- Each δ/2-ball contains at most one point of a δ-separated set
      have h_each_fin : ∀ c ∈ C, Set.Finite (Metric.ball c (δ/2) ∩ φ '' G) := by
        intro c hc
        by_contra h_inf_c
        have h_infinite_c : Set.Infinite (Metric.ball c (δ/2) ∩ φ '' G) :=
          Set.not_finite.mp h_inf_c
        -- An infinite set has two distinct elements
        have h_two : ∃ (x y : ℂ), x ∈ Metric.ball c (δ/2) ∩ φ '' G ∧
            y ∈ Metric.ball c (δ/2) ∩ φ '' G ∧ x ≠ y := by
          let f := Set.Infinite.natEmbedding (Metric.ball c (δ/2) ∩ φ '' G) h_infinite_c
          have h0 : (f 0).val ∈ Metric.ball c (δ/2) ∩ φ '' G := (f 0).property
          have h1 : (f 1).val ∈ Metric.ball c (δ/2) ∩ φ '' G := (f 1).property
          have hne : (f 0).val ≠ (f 1).val := by
            intro h_eq
            have h_eq' : f 0 = f 1 := Subtype.ext h_eq
            have : (0 : ℕ) = 1 := f.inj' h_eq'
            exact (by decide : (0 : ℕ) ≠ 1) this
          exact ⟨(f 0).val, (f 1).val, h0, h1, hne⟩
        rcases h_two with ⟨x, y, ⟨hx, hy, hxy⟩⟩
        have hxG : x ∈ φ '' G := hx.2
        have hyG : y ∈ φ '' G := hy.2
        have hdist : dist x y < δ := by
          calc
            dist x y ≤ dist x c + dist c y := dist_triangle _ _ _
            _ < δ/2 + δ/2 := by
              rw [dist_comm c y]
              exact add_lt_add (Metric.mem_ball.mp hx.1) (Metric.mem_ball.mp hy.1)
            _ = δ := by ring
        have hsep := hZ_sep x y hxG hyG hxy
        linarith
      -- φ''G is covered by the finite union of at-most-one-point sets, hence finite
      have h_cover' : φ '' G ⊆ ⋃ c ∈ C, (Metric.ball c (δ/2) ∩ φ '' G) := by
        intro x hx
        have hx_closedBall : x ∈ Metric.closedBall (0 : ℂ) M := h_sub hx
        rcases Set.mem_iUnion₂.mp (h_cover hx_closedBall) with ⟨c, hc, hx_ball⟩
        exact Set.mem_iUnion₂.mpr ⟨c, hc, Set.mem_inter hx_ball hx⟩
      apply h_inf
      exact Set.Finite.subset
        (Set.Finite.biUnion hC_fin (fun c hc => h_each_fin c hc))
        h_cover'
    -- From finiteness of φ(G) and injectivity of φ, G is finite
    let φ_emb : Λ ↪ ℂ := ⟨φ, hφ_inj⟩
    have h_fiber_fin : Set.Finite ((φ_emb : Λ → ℂ) ⁻¹' (φ '' G)) :=
      hZ_fin.preimage_embedding φ_emb
    have h_sub_G : G ⊆ (φ_emb : Λ → ℂ) ⁻¹' (φ '' G) := by
      intro g hg
      exact Set.mem_preimage.mpr (Set.mem_image_of_mem (φ_emb : Λ → ℂ) hg)
    exact Set.Finite.subset h_fiber_fin h_sub_G
  have h_N_fin : N_fun a₀ < ∞ := by
    dsimp [N_fun, ind]
    classical
    have heq : ∑' (g : Λ), B_R.indicator (fun _ => (1 : ℝ≥0∞)) (a₀ + (g : Fin f → ℂ)) =
        ∑ g ∈ hG_fin.toFinset, B_R.indicator (fun _ => (1 : ℝ≥0∞)) (a₀ + (g : Fin f → ℂ)) :=
      tsum_eq_sum fun g hg => by
        simp [show a₀ + (g : Fin f → ℂ) ∉ B_R from
          fun h => hg (hG_fin.mem_toFinset.mpr h)]
    rw [heq]
    have hle : ∑ g ∈ hG_fin.toFinset, B_R.indicator (fun _ => (1 : ℝ≥0∞)) (a₀ + (g : Fin f → ℂ)) ≤
        ∑ g ∈ hG_fin.toFinset, (1 : ℝ≥0∞) :=
      Finset.sum_le_sum fun g _ => by
        simp only [Set.indicator_apply]; split_ifs <;> simp
    exact lt_of_le_of_lt hle (by simp)
  let X : Set (Fin f → ℂ) := {x | ∃ (g : Λ), x = a₀ + (g : Fin f → ℂ) ∧ a₀ + (g : Fin f → ℂ) ∈ B_R}
  -- X is in bijection with G via a₀ + g
  have h_map : X = ((fun (g : Λ) => a₀ + (g : Fin f → ℂ)) '' G) := by
    ext x; constructor
    · intro hx
      dsimp [X] at hx
      rcases hx with ⟨g, hx_eq, hx_mem⟩
      subst hx_eq
      exact ⟨g, hx_mem, rfl⟩
    · intro hx
      rcases hx with ⟨g, hg, rfl⟩
      dsimp [X]
      exact ⟨g, rfl, hg⟩
  have hX_fin : Set.Finite X := by
    rw [h_map]
    exact hG_fin.image _
  -- X is nonempty: N_fun(a₀) ≠ 0 means ∃ g with a₀+g ∈ B_R
  have hX_ne : X.Nonempty := by
    have hN_ne : ¬∀ (g : Λ), ind B_R (a₀ + (g : Fin f → ℂ)) = 0 := by
      intro hall
      apply hN_pos
      exact ENNReal.tsum_eq_zero.mpr hall
    push Not at hN_ne
    obtain ⟨g, hg⟩ := hN_ne
    have hg_mem : a₀ + (g : Fin f → ℂ) ∈ B_R := by
      by_contra hmem
      apply hg
      classical
      exact if_neg hmem
    dsimp [X]
    exact ⟨a₀ + (g : Fin f → ℂ), ⟨g, rfl, hg_mem⟩⟩
  -- X ⊆ shift a₀ Λ.carrier ∩ polydisc f R
  have hX_sub : X ⊆ shift a₀ Λ.carrier ∩ polydisc f R := by
    intro x hx
    dsimp [X] at hx
    rcases hx with ⟨g, hg_eq, hx_B⟩
    subst hg_eq
    constructor
    · simp only [shift, Set.mem_setOf_eq]
      exact ⟨(g : Fin f → ℂ), g.2, rfl⟩
    · exact hx_B
  -- h_count: pairs (x,y) ∈ X² with y-x ∈ U are ≥ exp(γ/2*f) * |X|
  let I : Finset ((Fin f → ℂ) × (Fin f → ℂ)) :=
    (hX_fin.toFinset ×ˢ hX_fin.toFinset).filter
      (fun p : (Fin f → ℂ) × (Fin f → ℂ) => p.2 - p.1 ∈ U)
  have hE_card : E_fun a₀ = (I.card : ℝ≥0∞) := by
    -- The core combinatorial identity: E_fun(a₀) = |I|
    -- E_fun a₀ = ∑_{u∈U} ∑'_{g} ind(B_R ∩ {x|x+u∈B_R}) (a₀+g)
    -- = ∑_{u∈U} |{g∈G | a₀+g+u ∈ B_R}|
    -- = ∑_{u∈U} |{x∈X | x+u ∈ B_R}| (via x = a₀+g)
    -- Each (u,g) with a₀+g ∈ B_R, a₀+g+u ∈ B_R corresponds to pair (a₀+g, a₀+g+u) ∈ I
    -- and this is a bijection
    dsimp [E_fun, ind, I]
    -- E_fun a₀ = ∑ u ∈ U, ∑' (g : Λ), S_u u |>.indicator (fun _ => 1) (a₀ + g)
    classical
    let GV : Finset (Fin f → ℂ) := hG_fin.toFinset.image Subtype.val
    have h_inner (u : Fin f → ℂ) (hu : u ∈ U) :
        ∑' (g : Λ), (S_u u).indicator (fun _ => (1 : ℝ≥0∞)) (a₀ + (g : Fin f → ℂ))
        = ((GV.filter fun x => a₀ + x + u ∈ B_R).card : ℝ≥0∞) := by
      have h_support (g : Λ) : (S_u u).indicator (fun _ => (1 : ℝ≥0∞)) (a₀ + (g : Fin f → ℂ)) =
          if a₀ + (g : Fin f → ℂ) + u ∈ B_R ∧ g ∈ G then (1 : ℝ≥0∞) else 0 := by
        dsimp [S_u, G]; classical
        simp only [Set.indicator_apply, Set.mem_inter_iff, Set.mem_setOf_eq]
        congr 1; exact propext ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
      rw [tsum_congr (fun g => by rw [h_support g])]
      have h_support_finite (g : Λ) (hg : g ∉ hG_fin.toFinset) :
          (if a₀ + (g : Fin f → ℂ) + u ∈ B_R ∧ g ∈ G then (1 : ℝ≥0∞) else 0) = 0 := by
        have hgG : g ∉ G := by rwa [hG_fin.mem_toFinset] at hg
        simp [hgG]
      rw [tsum_eq_sum (s := hG_fin.toFinset) h_support_finite]
      have h_sum_simp : (∑ g ∈ hG_fin.toFinset,
          (if a₀ + (g : Fin f → ℂ) + u ∈ B_R ∧ g ∈ G then (1 : ℝ≥0∞) else 0)) =
          (∑ g ∈ hG_fin.toFinset, (if a₀ + (g : Fin f → ℂ) + u ∈ B_R then (1 : ℝ≥0∞) else 0)) := by
        refine Finset.sum_congr rfl (fun g hg => ?_)
        have hgG : g ∈ G := hG_fin.mem_toFinset.mp hg
        dsimp [G] at hgG ⊢
        simp [hgG]
      rw [h_sum_simp]
      have h_card_sum : (∑ g ∈ hG_fin.toFinset, (if a₀ + (g : Fin f → ℂ) + u ∈ B_R then (1 : ℝ≥0∞) else 0))
          = ((GV.filter fun x => a₀ + x + u ∈ B_R).card : ℝ≥0∞) := by
        have hinj : Set.InjOn Subtype.val (hG_fin.toFinset : Set Λ) := by
          intro x hx y hy h
          exact Subtype.ext h
        have hsum : (∑ g ∈ hG_fin.toFinset, (if a₀ + (g : Fin f → ℂ) + u ∈ B_R then (1 : ℝ≥0∞) else 0))
            = (∑ x ∈ GV, (if a₀ + x + u ∈ B_R then (1 : ℝ≥0∞) else 0)) := by
          dsimp [GV]
          have h := Finset.sum_image (f := fun x : Fin f → ℂ => if a₀ + x + u ∈ B_R then (1 : ℝ≥0∞) else 0) hinj
          simpa using h.symm
        have hsum2 : (∑ x ∈ GV, (if a₀ + x + u ∈ B_R then (1 : ℝ≥0∞) else 0))
            = ((GV.filter fun x => a₀ + x + u ∈ B_R).card : ℝ≥0∞) := by
          rw [← Finset.sum_filter, Finset.card_eq_sum_ones]
          simp
        calc
          (∑ g ∈ hG_fin.toFinset, (if a₀ + (g : Fin f → ℂ) + u ∈ B_R then (1 : ℝ≥0∞) else 0))
              = (∑ x ∈ GV, (if a₀ + x + u ∈ B_R then (1 : ℝ≥0∞) else 0)) := hsum
          _ = ((GV.filter fun x => a₀ + x + u ∈ B_R).card : ℝ≥0∞) := hsum2
      exact h_card_sum
    let J_filter (u : Fin f → ℂ) : Finset (Fin f → ℂ) := GV.filter fun x => a₀ + x + u ∈ B_R
    let J : Finset (Σ u : Fin f → ℂ, Fin f → ℂ) := Finset.sigma U J_filter
    have hJ_card : (J.card : ℝ≥0∞) = ∑ u ∈ U, ((GV.filter fun x => a₀ + x + u ∈ B_R).card : ℝ≥0∞) := by
      have h_nat : J.card = ∑ u ∈ U, (J_filter u).card := Finset.card_sigma U J_filter
      simpa [J_filter] using congrArg (fun n : ℕ => (n : ℝ≥0∞)) h_nat
    have h_bij : J.card = I.card := by
      -- Use card_bij directly
      refine Finset.card_bij (s := J) (t := I)
        (fun a _ha => (a₀ + a.2, a₀ + a.2 + a.1)) ?_ ?_ ?_
      · -- hi: image is in I
        intro a ha
        rcases Finset.mem_sigma.mp ha with ⟨hu, hg_mem⟩
        rcases Finset.mem_filter.mp hg_mem with ⟨hg_finset, hcond⟩
        -- hg_finset : a.2 ∈ GV = hG_fin.toFinset.image Subtype.val
        have ha2_mem_image : a.2 ∈ hG_fin.toFinset.image Subtype.val := by
          dsimp [GV] at hg_finset; exact hg_finset
        rcases Finset.mem_image.mp ha2_mem_image with ⟨g, hg_finset_orig, hg_val⟩
        -- hg_val : Subtype.val g = a.2
        dsimp [I]
        rw [Finset.mem_filter]
        constructor
        · rw [Finset.mem_product]
          constructor
          · -- a₀ + a.2 ∈ hX_fin.toFinset
            rw [hX_fin.mem_toFinset, h_map, ← hg_val]
            exact ⟨g, hG_fin.mem_toFinset.mp hg_finset_orig, rfl⟩
          · -- a₀ + a.2 + a.1 ∈ hX_fin.toFinset
            have hu_Λ : a.1 ∈ Λ := hU_in_Λ a.1 hu
            let g' : Λ := g + ⟨a.1, hu_Λ⟩
            have hg'G : g' ∈ G := by
              dsimp [G, g']
              rw [← hg_val] at hcond
              simpa [add_assoc] using hcond
            have h_eq : a₀ + (g' : Fin f → ℂ) = a₀ + a.2 + a.1 := by
              dsimp [g']; rw [hg_val]; simp [add_assoc]
            rw [hX_fin.mem_toFinset, h_map]
            exact ⟨g', hg'G, h_eq⟩
        · -- (a₀ + a.2 + a.1) - (a₀ + a.2) = a.1 ∈ U
          have : (a₀ + a.2 + a.1) - (a₀ + a.2) = a.1 := by abel
          rw [this]
          exact hu
      · -- i_inj
        intro a₁ ha₁ a₂ ha₂ h_eq
        rcases Finset.mem_sigma.mp ha₁ with ⟨hu₁, hg₁⟩
        rcases Finset.mem_sigma.mp ha₂ with ⟨hu₂, hg₂⟩
        rcases Prod.mk.inj h_eq with ⟨h_first, h_second⟩
        have hg_eq : a₁.2 = a₂.2 := add_left_cancel h_first
        have hu_eq : a₁.1 = a₂.1 := by
          rw [hg_eq] at h_second
          exact add_left_cancel h_second
        exact Sigma.ext hu_eq (heq_of_eq hg_eq)
      · -- i_surj
        intro p hp
        rw [Finset.mem_filter] at hp
        rcases hp with ⟨hp_prod, hpU⟩
        rcases Finset.mem_product.mp hp_prod with ⟨hx, hy⟩
        rw [hX_fin.mem_toFinset, h_map] at hx hy
        rcases hx with ⟨gx, hgxG, hx_eq⟩
        rcases hy with ⟨gy, hgyG, hy_eq⟩
        have hx_eq' : p.1 = a₀ + (gx : Fin f → ℂ) := by simpa using hx_eq.symm
        have hy_eq' : p.2 = a₀ + (gy : Fin f → ℂ) := by simpa using hy_eq.symm
        let u := p.2 - p.1
        have hu_U : u ∈ U := by
          simpa [u] using hpU
        have hgx_finset : gx ∈ hG_fin.toFinset := hG_fin.mem_toFinset.mpr hgxG
        have hgx_GV : (gx : Fin f → ℂ) ∈ GV := by
          dsimp [GV]
          exact Finset.mem_image.mpr ⟨gx, hgx_finset, rfl⟩
        have ha0gxu_BR : a₀ + (gx : Fin f → ℂ) + u ∈ B_R := by
          have h_eq_temp : a₀ + (gx : Fin f → ℂ) + (p.2 - p.1) = a₀ + (gy : Fin f → ℂ) := by
            rw [hx_eq', hy_eq']; abel
          dsimp [u]; rw [h_eq_temp]; exact hgyG
        refine ⟨⟨u, (gx : Fin f → ℂ)⟩, Finset.mem_sigma.mpr ⟨hu_U,
          Finset.mem_filter.mpr ⟨hgx_GV, ha0gxu_BR⟩⟩, ?_⟩
        ext x
        · simpa using congrArg (fun f => f x) hx_eq'.symm
        · dsimp [u]
          have h_eq : a₀ + (gx : Fin f → ℂ) + (p.2 - p.1) = p.2 := by
            calc
              a₀ + (gx : Fin f → ℂ) + (p.2 - p.1) = a₀ + (gy : Fin f → ℂ) := by
                rw [hx_eq', hy_eq']; abel
              _ = p.2 := hy_eq'.symm
          simpa using congrArg (fun f => f x) h_eq
    calc
      ∑ u ∈ U, ∑' (g : Λ), (S_u u).indicator (fun _ => (1 : ℝ≥0∞)) (a₀ + (g : Fin f → ℂ))
          = ∑ u ∈ U, ((GV.filter fun x => a₀ + x + u ∈ B_R).card : ℝ≥0∞) := by
        refine Finset.sum_congr rfl (fun u hu => by rw [h_inner u hu])
      _ = (J.card : ℝ≥0∞) := by
        rw [← hJ_card]
      _ = (I.card : ℝ≥0∞) := by
        simp [h_bij]

  have hX_card : (hX_fin.toFinset.card : ℝ≥0∞) = (hG_fin.toFinset.card : ℝ≥0∞) := by
    have heq : hX_fin.toFinset = hG_fin.toFinset.image (fun g : Λ => a₀ + (g : Fin f → ℂ)) := by
      ext x
      simp [Finset.mem_image, hG_fin.mem_toFinset, h_map, Set.mem_image]
    have hcard : hX_fin.toFinset.card = hG_fin.toFinset.card := by
      rw [heq]
      classical
      exact Finset.card_image_of_injective _ (fun g₁ g₂ h => Subtype.ext (add_left_cancel h))
    exact_mod_cast hcard
  have hN_card : N_fun a₀ = (hX_fin.toFinset.card : ℝ≥0∞) := by
    dsimp [N_fun, ind]
    classical
    have h_tsum_eq : ∑' (g : Λ), B_R.indicator (fun _ => (1 : ℝ≥0∞)) (a₀ + (g : Fin f → ℂ))
        = ∑ g ∈ hG_fin.toFinset, (1 : ℝ≥0∞) := by
      rw [tsum_eq_sum (s := hG_fin.toFinset) (fun g hg => by
        simp [show a₀ + (g : Fin f → ℂ) ∉ B_R from
          fun h => hg (hG_fin.mem_toFinset.mpr h)])]
      apply Finset.sum_congr rfl
      intro g hg
      have hgB : a₀ + (g : Fin f → ℂ) ∈ B_R := hG_fin.mem_toFinset.mp hg
      simp [hgB]
    rw [h_tsum_eq, hX_card]
    simp
  have h_count : ((I.card : ℝ) ≥ Real.exp (γ / 2 * (f : ℝ)) * hX_fin.toFinset.card) := by
    -- From hE_ge and the equalities above
    -- hE_ge : E_fun a₀ ≥ c * N_fun a₀  (in ℝ≥0∞)
    rw [hE_card, hN_card] at hE_ge
    -- hE_ge : (I.card : ℝ≥0∞) ≥ c * (hX_fin.toFinset.card : ℝ≥0∞)
    have h_right_fin : c * (hX_fin.toFinset.card : ℝ≥0∞) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)
    have h_left_fin : (I.card : ℝ≥0∞) ≠ ∞ := by simp
    have htoReal := (ENNReal.toReal_le_toReal h_right_fin h_left_fin).mpr hE_ge
    simp [c, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _),
      ENNReal.toReal_natCast] at htoReal
    -- htoReal : Real.exp (γ / 2 * ↑f) * ↑(hX_fin.toFinset.card) ≤ ↑(I.card)
    -- But the goal is: ↑(I.card) ≥ Real.exp (γ / 2 * ↑f) * ↑(hX_fin.toFinset.card)
    -- These are equivalent
    exact htoReal
  exact ⟨a₀, X, hX_sub, hX_fin, hX_ne, h_count⟩

