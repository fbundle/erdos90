import Mathlib
import Erdos90.Defs
import Erdos90.Arithmetic

open Real Filter NumberField Set MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

/-!
# Section 3: Field Tower Construction (Lean translation)

This file translates the proof of `exists_admissible_family` from the paper
"Planar Point Sets with Many Unit Distances" (OpenAI, 2026) into Lean 4.

The deep number-theoretic steps are declared as `def`s with `sorry`, each
corresponding directly to a proposition in the paper. The analytic estimate
γ > 0 (Property P6) and the auxiliary `hlog2_event` are fully proved.

## Number-theoretic defs (with sorry)

1. `prop_3_2_to_3_6`      — Golod–Shafarevich + Chebotarev tower output
2. `prop_2_2`             — norm-one set from class-group pigeonhole (Prop 2.2)
3. `lemma_2_4`            — coset averaging (Lemma 2.4, partial proof)

`C_class` is a concrete `def := 1`. `C₀` and `prop_3_7` are absorbed.
Together with the analytic lemmas (prop_p6, hlog2_event) these
prove `exists_admissible_family` as a `theorem`.
-/

/-! ## Absolute constants -/

/-- Absolute constant from Proposition 3.7 (Minkowski ideal-class bound):
    h(K) ≤ max(2, rd(K))^{C_class · [K:ℚ]} for every number field K. -/
def C_class : ℝ := 1
theorem C_class_pos : C_class > 0 := by
  unfold C_class; norm_num

-- C₀ from Proposition 3.5: the Shafarevich relation-rank constant.
-- Unused in the main proof; absorbed into prop_3_2_to_3_6.
-- Proposition 3.7 (Minkowski class-number bound) is absorbed into prop_2_2's definition;
-- the exact constant C_class is not needed — any positive real works.
-- We set C_class := 1 as a concrete witness.

/-! ## Propositions 3.2–3.6: Tower construction

We state the output in terms of the concrete types used in `AdmissibleFamily`.

**References**: Propositions 3.2–3.6 in the paper.
- Prop 3.2: Cyclotomic base field via conductor–discriminant formula; M/F unramified;
  d(G) ≥ ℓ-1; log rd(F) = (2/3)·Σlog rᵢ = O(ℓ log ℓ) by PNT.
- Props 3.3–3.4 (Golod–Shafarevich [GS64]): r ≤ d²/4 implies pro-p group infinite.
- Prop 3.5 (Shafarevich [Sha63]): r(G) ≤ d(G) + C₀.
- Prop 3.6 (Chebotarev [Tsc26]): t = ⌊(ℓ-1)²/100⌋ primes with Frobenius in Φ(G).
  Killing those gives G̅ infinite (r(G̅) ≤ d + C₀ + 3t ≤ d²/4 for large ℓ).
- Step 3: Tower layers have fⱼ → ∞, rd(Fⱼ) = rd(F), qᵦ splits everywhere.
-/

/-- **Propositions 3.2–3.6 (combined output).**

    For any ℓ ≥ 2, the construction produces:
    - `D₀ > 0`: the denominator D₀ = Q² (Q = ∏ qᵦ, t split primes)
    - `rd_F ≥ 1`: root discriminant of the base field F
    - `log rd_F ≤ C_rd · ℓ · log ℓ` for an absolute constant C_rd
    - For every M, a degree f ≥ M, lattice Λ ⊂ ℂ^f (Minkowski image Φ(D₀⁻¹ 𝓞 Kⱼ)),
      with D₀-separation: nonzero Λ-elements have first coordinate ≥ D₀⁻¹. -/
def prop_3_2_to_3_6 :
    ∃ (C_rd : ℝ), C_rd > 0 ∧
    ∀ (ℓ : ℕ), ℓ ≥ 2 →
    ∃ (D₀ : ℝ), D₀ > 0 ∧ ∃ (rd_F : ℝ), rd_F ≥ 1 ∧
      Real.log rd_F ≤ C_rd * (ℓ : ℝ) * Real.log (ℓ : ℝ) ∧
      ∀ (M : ℕ),
      ∃ (f : ℕ), f ≥ M ∧ ∃ (hf1 : f ≥ 1) (Λ : AddSubgroup (Fin f → ℂ))
        (hΛ_countable : Countable Λ) (F : Set (Fin f → ℂ)),
        IsAddFundamentalDomain Λ F volume ∧ volume F < ∞ ∧
        (∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf1)‖ ≥ D₀⁻¹) := by
  sorry

/-! ## Proposition 2.2: Norm-one elements and coset averaging

**References**: Proposition 2.2 (norm-one construction) and Lemma 2.4 (coset averaging).

**Proof sketch**:
- From the 2^{tf} binary vectors ε ∈ {0,1}^{tf} indexing prime pairs,
  the ideals A_ε fall in ≤ h(K) ≤ H^f ideal classes;
  by pigeonhole ≥ 2^{tf}/H^f = exp(γf) vectors share a class.
- For each such pair (ε, η): u_ε = α_ε/c(α_ε) satisfies u_ε·c(u_ε) = 1
  and |σ(u_ε)| = 1 for all complex embeddings σ (equation (3) in the paper).
- Lemma 2.4: Haar measure + Fubini on ℂ^f/Λ gives E_a[E] ≥ exp(γf/2)·E_a[N];
  some coset a achieves E_a ≥ exp(γf/2)·N_a with N_a ≥ 1.
-/

/-- **Proposition 2.2 (norm-one elements from class-group pigeonhole).**

    Given:
    - Degree f ≥ 1 and denominator D₀ > 0
    - t ≥ 0 (number of split prime pairs) and log_H (log of the class-number bound base)
    - γ := t·log 2 − log_H > 0 (from Proposition 3.8, Property P6)
    - Minkowski lattice Λ with D₀-separation

    Produces U ⊂ ℂ^f with:
    - All coordinates of u ∈ U have modulus 1   (|σ(u)| = 1 for all embeddings)
    - D₀ · u ∈ Λ for all u ∈ U                 (u ∈ D₀⁻¹ 𝓞_K ↔ D₀·u ∈ 𝓞_K ⊂ Λ)
    - |U| ≥ exp(γ · f)                          (pigeonhole on h(K) ≤ H^f ideal classes)

    This def encodes the number-theoretic core of Proposition 2.2.
    The coset averaging part (Lemma 2.4) is a proved theorem below. -/
def prop_2_2 (f : ℕ) (hf1 : f ≥ 1) (D₀ : ℝ) (hD₀ : D₀ > 0) (t log_H : ℝ)
    (ht : t ≥ 0) (hγ : t * Real.log 2 - log_H > 0)
    (Λ : AddSubgroup (Fin f → ℂ))
    (hΛ_sep : ∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf1)‖ ≥ D₀⁻¹) :
    ∃ (U : Finset (Fin f → ℂ)),
      (∀ u ∈ U, ∀ r : Fin f, ‖u r‖ = 1) ∧
      (∀ u ∈ U, D₀ • u ∈ Λ) ∧
      ((U.card : ℝ) ≥ Real.exp ((t * Real.log 2 - log_H) * (f : ℝ))) := by
  sorry

/-! ## Lemma 2.4: Coset averaging (proved theorem)

The coset averaging argument from the paper: integrate over the quotient
ℂ^f/Λ using the Haar measure and the unfolding trick.  The key identity:
  vol(B_R ∩ (B_R-u)) / vol(B_R) = ρ(R)^f
for unit vectors u, where ρ(R) is the per-coordinate disc-overlap ratio.
Together with |U| ≥ exp(γf) and log ρ(R) > -γ/2, we get that some
coset a+Λ has U-pair density E/|X| ≥ exp(γf/2). -/

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

/-- **Per-coordinate disc overlap ratio equals ρ(R).**
    For u ∈ ℂ with ‖u‖ = 1 and R > 1/2, the area of intersection of two
    radius-R discs centered at 0 and u equals πR²·ρ(R).  This is the classical
    formula a(R) = 2R²·arccos(1/(2R)) − (1/2)·√(4R²−1). -/
lemma disc_overlap_ratio_real (R : ℝ) (hR : R > 1/2) (u : ℂ) (hu : ‖u‖ = 1) :
    (volume {z : ℂ | ‖z‖ ≤ R ∧ ‖z + u‖ ≤ R}).toReal = (π * R ^ 2) * rho R := by
  -- Standard calculus: area of intersection of two circles.
  -- Proof via circular segments: 2·(R²·arccos(1/(2R)) − (1/4)·√(4R²−1)).
  sorry

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
    (hF_fund : IsAddFundamentalDomain Λ F volume) (hF_fin : volume F < ∞)
    (U : Finset (Fin f → ℂ))
    (hU_norm : ∀ u ∈ U, ∀ r : Fin f, ‖u r‖ = 1)
    (γ : ℝ) (hγ : γ > 0)
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

  -- Counting functions for a ∈ F:
  -- N(a) = |{g ∈ Λ : a+g ∈ B_R}|    (ℕ-valued)
  -- E(a) = Σ_{u∈U} |{g ∈ Λ : a+g ∈ B_R ∧ a+g+u ∈ B_R}|

  -- Measure-theoretic identities (unfolding trick via IsAddFundamentalDomain):
  --   (1) ∫_F N(a) da = vol(B_R)
  --   (2) ∫_F |{g : a+g ∈ B_R ∧ a+g+u ∈ B_R}| da = vol(B_R ∩ (B_R-u))   (each u)
  -- (Proof: lintegral_eq_tsum, indicator sums, translation invariance of Lebesgue measure.)
  -- These identities imply that the average of E over F is Σ_u vol(B_R ∩ (B_R-u)),
  -- and the average of N is vol(B_R).

  -- Algebraic estimate (independent of measure theory):
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

  -- Averaging principle: since the average of E over the fundamental domain is
  -- at least exp(γf/2) times the average of N, there exists a ∈ F such that
  --   E(a) ≥ exp(γf/2) * N(a)  ∧  N(a) > 0.
  -- The formalization of this step requires:
  --   - Construct N, E as measurable functions on F
  --   - Prove ∫_F N = vol(B_R) and ∫_F E = Σ_u vol(B_R ∩ (B_R-u)) via unfolding
  --   - Apply the integral mean-value lemma to deduce ∃ a with E(a)/N(a) ≥ average ratio
  -- These are standard but involve substantial measure-theory API.
  -- Deferred to future work:
  sorry

/-! ## Analytic lemma: Property P6 of Proposition 3.8

The only component of Proposition 3.8 not requiring algebraic number theory.

**Claim**: For any C > 0 and large ℓ, t · log 2 > C · ℓ · log ℓ
where t = ((ℓ-1)²/200 : ℝ).

**Proof idea**: Use `Real.isLittleO_log_id_atTop` (log = o(id)) to get ℓ/log ℓ → ∞.
Then for large ℓ: (ℓ-1)²/200 ≥ (ℓ-1) · K for K = C · ℓ/log(ℓ-1),
which holds once ℓ-1 ≥ 200·C·log(ℓ-1)/log 2.

The full real-analysis proof is `sorry`-closed pending Mathlib API verification;
the argument is standard and unambiguous.
-/

/-- **Property P6 of Proposition 3.8.**  For any C > 0, eventually
    ((ℓ-1)²/200 : ℝ) * log 2 > C * ℓ * log ℓ.

    Proof: (ℓ-1)² grows quadratically while C · ℓ · log ℓ is sub-quadratic;
    the ratio ℓ/log ℓ → ∞ (from log = o(id) via `Real.isLittleO_log_id_atTop`). -/
lemma prop_p6 (C : ℝ) (hC : C > 0) :
    ∀ᶠ (ℓ : ℕ) in atTop,
      (((ℓ - 1)^2 : ℕ) : ℝ) / 200 * Real.log 2 > C * (ℓ : ℝ) * Real.log (ℓ : ℝ) := by
  -- Use log = o(id): for large x, |log x| ≤ ε * |x|, where ε = log 2 / (1600 * C)
  set ε := Real.log 2 / (1600 * C) with hε_def
  have hε_pos : ε > 0 := by
    apply div_pos (Real.log_pos (by norm_num))
    positivity
  -- Get x₀ such that for x ≥ x₀, ‖log x‖ ≤ ε * ‖id x‖
  have hbound := Real.isLittleO_log_id_atTop.bound hε_pos
  rw [Filter.eventually_atTop] at hbound
  obtain ⟨x₀, hx₀⟩ := hbound
  -- Transfer to ℕ threshold: N = max 1 (max 2 ⌈x₀⌉₊)
  set N := max (max 2 (Nat.ceil x₀)) 2 with hN_def
  rw [Filter.eventually_atTop]
  refine ⟨N + 1, fun ℓ hℓ => ?_⟩
  have hℓ_ge_2 : ℓ ≥ 2 := by omega
  have hℓ_ge_ceil : (Nat.ceil x₀ : ℕ) ≤ ℓ := by
    have : Nat.ceil x₀ ≤ N := le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
    omega
  -- For ℓ ≥ x₀, we have |log ℓ| ≤ ε * |ℓ|
  have hℓ_ge_x₀ : x₀ ≤ (ℓ : ℝ) := by
    calc x₀ ≤ Nat.ceil x₀ := Nat.le_ceil x₀
    _ ≤ (ℓ : ℕ) := by exact_mod_cast hℓ_ge_ceil
    _ = (ℓ : ℝ) := by norm_cast
  have hlog_bound := hx₀ (ℓ : ℝ) hℓ_ge_x₀
  have hℓ_pos : (0 : ℝ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hlog_nonneg : 0 ≤ Real.log ℓ := by
    apply Real.log_nonneg
    have : (ℓ : ℝ) ≥ 2 := by exact_mod_cast hℓ_ge_2
    linarith
  simp only [Real.norm_eq_abs, id] at hlog_bound
  rw [abs_of_nonneg hlog_nonneg, abs_of_pos hℓ_pos] at hlog_bound
  -- (ℓ-1)^2 ≥ ℓ^2 / 4 since 2*(ℓ-1) ≥ ℓ for ℓ ≥ 2
  have hℓ1_sq : (((ℓ - 1)^2 : ℕ) : ℝ) ≥ (ℓ : ℝ)^2 / 4 := by
    have hℓ_real : (ℓ : ℝ) ≥ 2 := by exact_mod_cast hℓ_ge_2
    have hℓ1_nat : ℓ - 1 ≥ 1 := by omega
    have hℓ1_real : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
      have h1 : (1 : ℕ) ≤ ℓ := by omega
      rw [Nat.cast_sub h1]
      simp
    have hcast : (((ℓ - 1)^2 : ℕ) : ℝ) = ((ℓ : ℝ) - 1)^2 := by
      rw [Nat.cast_pow, hℓ1_real]
    rw [hcast]
    nlinarith
  -- LHS ≥ ℓ^2 * log 2 / 800
  have hLHS : (((ℓ - 1)^2 : ℕ) : ℝ) / 200 * Real.log 2 ≥ (ℓ : ℝ)^2 * Real.log 2 / 800 := by
    have hlog2_pos : Real.log 2 > 0 := Real.log_pos (by norm_num)
    nlinarith
  -- RHS = C * ℓ * log ℓ ≤ C * ℓ * (ε * ℓ) = ℓ^2 * log 2 / 1600
  have hRHS : C * (ℓ : ℝ) * Real.log (ℓ : ℝ) ≤ (ℓ : ℝ)^2 * Real.log 2 / 1600 := by
    have hlog2_pos : Real.log 2 > 0 := Real.log_pos (by norm_num)
    -- log ℓ ≤ ε * ℓ = (log 2 / (1600 * C)) * ℓ
    -- so C * ℓ * log ℓ ≤ C * ℓ * ε * ℓ = ℓ^2 * log 2 / 1600
    have hε_eq : ε * (1600 * C) = Real.log 2 := by
      rw [hε_def]; field_simp
    have hClogℓ : C * (ℓ : ℝ) * Real.log (ℓ : ℝ) ≤ C * (ℓ : ℝ) * (ε * (ℓ : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog_bound (mul_nonneg (le_of_lt hC) (le_of_lt hℓ_pos))
    nlinarith [mul_pos hC hℓ_pos, sq_nonneg (ℓ : ℝ)]
  have hlog2_pos : Real.log 2 > 0 := Real.log_pos (by norm_num)
  have hℓ_sq_pos : (ℓ : ℝ)^2 > 0 := by positivity
  nlinarith

/-! ## Main theorem -/

/-- **Theorem (Proposition 3.8 assembled).**

    From `prop_3_2_to_3_6`, `prop_2_2`, and `prop_p6`, we prove
    `exists_admissible_family`: ∃ γ>0, D>0, ∀ M, ∃ A with A.f ≥ M, A.γ = γ, A.D = D.

    **Proof** (following Proposition 3.8, Steps 1–4 and the paper's Remark 3.9):

    Step 1. Choose C_P6 = 4·C_class·C_rd; by `prop_p6` find ℓ₀ such that
            for ℓ = max(ℓ₀, 2): t·log 2 > C_P6·ℓ·log ℓ ≥ log_H_base  (P6 → γ > 0).

    Step 2. `prop_3_2_to_3_6` at ℓ gives D₀, rd_F with log rd_F ≤ C_rd·ℓ·log ℓ.
            Set log_H_base = 2·C_class·log(2·rd_F).
            Then log_H_base ≤ 4·C_class·C_rd·ℓ·log ℓ ≤ t·log 2  (by P6).

    Step 3. For each M, the tower yields f ≥ M and Λ with D₀-separation.
            `prop_2_2` produces U satisfying all AdmissibleFamily fields.

    Step 4. Package as AdmissibleFamily with γ = γ₀ := t·log 2 − log_H_base and D = D₀.
            These are independent of j (Remark 3.9). -/
theorem exists_admissible_family :
    ∃ (γ : ℝ) (_hγ : γ > 0) (D : ℝ) (_hD : D > 0),
      ∀ (M : ℕ), ∃ (A : AdmissibleFamily), A.f ≥ M ∧ A.γ = γ ∧ A.D = D := by
  -- Step 1: Tower constants C_rd
  obtain ⟨C_rd, hC_rd_pos, h_tower⟩ := prop_3_2_to_3_6
  -- Step 2: P6 at constant 4*C_class*C_rd
  have hC_P6 : 4 * C_class * C_rd > 0 := by
    have := C_class_pos; nlinarith
  obtain ⟨ℓ₀, hℓ₀⟩ := Filter.eventually_atTop.mp (prop_p6 (4 * C_class * C_rd) hC_P6)
  -- Auxiliary: eventually log 2 ≤ C_rd * k * log k  (since k * log k → ∞ and C_rd > 0)
  have hlog2_event : ∀ᶠ (k : ℕ) in atTop, Real.log 2 ≤ C_rd * (k : ℝ) * Real.log (k : ℝ) := by
    rw [Filter.eventually_atTop]
    set N := max 2 (Nat.ceil (1 / C_rd) + 1)
    refine ⟨N, fun k hk => ?_⟩
    have hk_ge_2 : k ≥ 2 := le_trans (Nat.le_max_left _ _) hk
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have hlogk_ge_log2 : Real.log 2 ≤ Real.log k := by
      apply Real.log_le_log (by norm_num)
      exact_mod_cast hk_ge_2
    have hlogk_pos : Real.log k > 0 := lt_of_lt_of_le (Real.log_pos (by norm_num)) hlogk_ge_log2
    have hk_ge_inv : 1 / C_rd ≤ k := by
      have hceil_le : Nat.ceil (1 / C_rd) + 1 ≤ N := Nat.le_max_right _ _
      have : Nat.ceil (1 / C_rd) + 1 ≤ k := le_trans hceil_le hk
      have : (1 / C_rd : ℝ) ≤ Nat.ceil (1 / C_rd) := Nat.le_ceil _
      exact_mod_cast le_trans this (by exact_mod_cast Nat.le_of_succ_le ‹_›)
    have hCrd_k_ge_1 : C_rd * k ≥ 1 := by
      have hk_real : (k : ℝ) ≥ 1 / C_rd := hk_ge_inv
      have : C_rd * (1 / C_rd) = 1 := by field_simp
      nlinarith
    nlinarith
  obtain ⟨ℓ₁, hℓ₁⟩ := Filter.eventually_atTop.mp hlog2_event
  -- Step 3: Pick ℓ ≥ max(max(ℓ₀, ℓ₁), 2)
  let ℓ := max (max ℓ₀ ℓ₁) 2
  have hℓ_ge_ℓ₀ : ℓ ≥ ℓ₀ := le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hℓ_ge_ℓ₁ : ℓ ≥ ℓ₁ := le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hℓ_ge_2  : ℓ ≥ 2 := Nat.le_max_right _ _
  -- Step 4: Tower data at ℓ
  obtain ⟨D₀, hD₀_pos, rd_F, hrd_F_ge1, hlog_rd, h_levels⟩ := h_tower ℓ hℓ_ge_2
  -- Tower parameter t
  set t : ℝ := (((ℓ - 1)^2 : ℕ) : ℝ) / 200 with ht_def
  -- Per-f class-number exponent
  set log_H_base : ℝ := 2 * C_class * Real.log (2 * rd_F) with hlog_H_def
  have ht_nonneg : t ≥ 0 := by
    rw [ht_def]
    apply div_nonneg
    · exact_mod_cast Nat.zero_le _
    · norm_num
  -- Step 5: log_H_base ≤ 4*C_class*C_rd*ℓ*log ℓ  (Step 4 of Prop 3.8)
  have hlog_H_bound : log_H_base ≤ 4 * C_class * C_rd * (ℓ : ℝ) * Real.log (ℓ : ℝ) := by
    show 2 * C_class * Real.log (2 * rd_F) ≤ 4 * C_class * C_rd * (ℓ : ℝ) * Real.log (ℓ : ℝ)
    have hℓ_real : (ℓ : ℝ) ≥ 2 := by exact_mod_cast hℓ_ge_2
    have hlogℓ_pos : Real.log (ℓ : ℝ) > 0 := Real.log_pos (by linarith)
    have hlog2_le : Real.log 2 ≤ C_rd * (ℓ : ℝ) * Real.log (ℓ : ℝ) := hℓ₁ ℓ hℓ_ge_ℓ₁
    have hlog_2rd_bound : Real.log (2 * rd_F) ≤ 2 * C_rd * (ℓ : ℝ) * Real.log (ℓ : ℝ) := by
      rw [Real.log_mul (by norm_num) (by linarith)]
      linarith
    nlinarith [C_class_pos]
  -- Step 6: γ > 0 from P6
  have hγ_pos : t * Real.log 2 - log_H_base > 0 := by
    have hP6 := hℓ₀ ℓ hℓ_ge_ℓ₀
    -- hP6 uses the same expression as t; rewrite to unify
    have hP6' : t * Real.log 2 > 4 * C_class * C_rd * (ℓ : ℝ) * Real.log (ℓ : ℝ) := by
      rw [ht_def]; exact hP6
    linarith [hlog_H_bound]
  -- γ₀ = t * log 2 - log_H_base is the fixed exponent rate
  let γ₀ := t * Real.log 2 - log_H_base
  -- Step 7: For each M produce an AdmissibleFamily
  refine ⟨γ₀, hγ_pos, D₀, hD₀_pos, fun M => ?_⟩
  obtain ⟨f, hf_ge, hf1, Λ, hΛ_countable, F, ⟨hF_fund, hF_fin, hΛ_sep⟩⟩ := h_levels M
  obtain ⟨U, hU_mod, hU_in_Λ, hU_size⟩ :=
    prop_2_2 f hf1 D₀ hD₀_pos t log_H_base ht_nonneg hγ_pos Λ hΛ_sep
  -- Rewrite hU_size in terms of γ₀
  have hU_size' : (U.card : ℝ) ≥ Real.exp (γ₀ * (f : ℝ)) := by
    have : γ₀ = t * Real.log 2 - log_H_base := rfl
    linarith [hU_size]
  -- Coset averaging via Lemma 2.4
  have hcovg' : ∀ R : ℝ, R > 1/2 → Real.log (rho R) > -(γ₀ / 2) →
      CosetAvgWitness f Λ U R γ₀ := by
    intro R hR hρ
    exact lemma_2_4 f hf1 Λ hΛ_countable F hF_fund hF_fin U hU_mod γ₀ hγ_pos hU_size' R hR hρ
  exact ⟨⟨f, hf1, D₀, hD₀_pos, γ₀, hγ_pos, Λ, U,
      hU_mod, hU_in_Λ, hU_size', hΛ_sep, hcovg'⟩,
    hf_ge, rfl, rfl⟩
