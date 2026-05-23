import Mathlib
import Erdos90.Defs
import Erdos90.Arithmetic
import Erdos90.DiscGeometry
import Erdos90.CosetAveraging
import Erdos90.NumberFieldDeep

open Real Filter NumberField Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal Topology Complex intervalIntegral Pointwise

noncomputable section

/-!
# Section 3: Field Tower Construction (Lean translation)

This file translates the proof of `exists_admissible_family` from the paper
"Planar Point Sets with Many Unit Distances" (OpenAI, 2026) into Lean 4.

The deep number-theoretic steps are `def`s with `sorry` in `NumberFieldDeep.lean`:

1. `golod_shafarevich_tower_with_lattice` — Props 3.2–3.6: Golod–Shafarevich +
   Chebotarev tower, Minkowski lattice, type bridge
2. `cm_norm_one_elements` — Prop 2.2: norm-one set from class-group pigeonhole

These are assembled as `prop_3_2_to_3_6` (this file) providing both the tower data
and a Prop-2.2 callback.  Lemma 2.4 (coset averaging) is fully proved in
`CosetAveraging.lean`.

The analytic estimate γ > 0 (Property P6) and `hlog2_event` are fully proved below.
`C_class` is a concrete `def := 1`.

Together these prove `exists_admissible_family` as a `theorem`.
-/

/-! ## Absolute constants -/

/-- Absolute constant from Proposition 3.7 (Minkowski ideal-class bound):
    h(K) ≤ max(2, rd(K))^{C_class · [K:ℚ]} for every number field K. -/
def C_class : ℝ := 1
theorem C_class_pos : C_class > 0 := by
  unfold C_class; norm_num

-- C₀ from Proposition 3.5: the Shafarevich relation-rank constant.
-- Unused in the main proof; absorbed into prop_3_2_to_3_6.
-- Proposition 3.7 (Minkowski class-number bound) is absorbed into the tower's Prop-2.2 callback;
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

/-- **Propositions 3.2–3.6 (tower) + Proposition 2.2 (norm-one elements, via callback).**

    For any ℓ ≥ 2, the Golod–Shafarevich + Chebotarev construction produces:
    - `C_rd = 1`: absolute constant (log bound proved via `log_two_mul_le`)
    - `D₀ > 0`: denominator Q² (Q = ∏_{b=1}^t q_b, product of split primes)
    - `rd_F ≥ 1`: root discriminant of the base cubic field F, with
      `log rd_F ≤ C_rd · ℓ · log ℓ`

    For every M, a tower level `f ≥ M` with:
    - `Λ ⊂ ℂ^f`: Minkowski lattice Φ_j(D₀⁻¹ · 𝓞_{K_j}) for the CM field K_j = F_j(i)
    - `F ⊂ ℂ^f`: fundamental domain of Λ (IsAddFundamentalDomain, finite volume)
    - `∀ v ∈ Λ, v ≠ 0 → ‖v(fin0 hf1)‖ ≥ D₀⁻¹` (product-formula separation)

    It also provides a **callback** for Prop 2.2: given `t` and `log_H`
    (the tower parameters, defined externally from ℓ and rd_F) with
    `γ := t·log 2 − log_H > 0`, the callback returns the norm-one set `U`
    from the class-group pigeonhole on K_j.

    **Lean gaps** (two sorries in NumberFieldDeep.lean):
    (a) `golod_shafarevich_tower_with_lattice`: Golod–Shafarevich pro-3 tower +
        Chebotarev split primes + type bridge `mixedSpace K_j ≃ Fin f_j → ℂ`
        (not in Mathlib v4.29.1)
    (b) `cm_norm_one_elements`: CM split-prime ideal pairs + class-group
        pigeonhole for U (not in Mathlib v4.29.1) -/
def prop_3_2_to_3_6 :
    ∃ (C_rd : ℝ), C_rd > 0 ∧
    ∀ (ℓ : ℕ), ℓ ≥ 2 →
    ∃ (D₀ : ℝ), D₀ > 0 ∧ ∃ (rd_F : ℝ), rd_F ≥ 1 ∧
      Real.log rd_F ≤ C_rd * (ℓ : ℝ) * Real.log (ℓ : ℝ) ∧
      ∀ (M : ℕ),
      ∃ (f : ℕ), f ≥ M ∧ ∃ (hf1 : f ≥ 1) (Λ : AddSubgroup (Fin f → ℂ))
        (_ : Countable Λ) (F : Set (Fin f → ℂ)),
        IsAddFundamentalDomain Λ F volume ∧ volume F < ∞ ∧
        (∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf1)‖ ≥ D₀⁻¹) ∧
        ∀ (t log_H : ℝ), t ≥ 0 → (t * Real.log 2 - log_H > 0) →
        ∃ (U : Finset (Fin f → ℂ)),
          (∀ u ∈ U, ∀ r : Fin f, ‖u r‖ = 1) ∧
          (∀ u ∈ U, (u : Fin f → ℂ) ∈ Λ) ∧
          ((U.card : ℝ) ≥ Real.exp ((t * Real.log 2 - log_H) * (f : ℝ))) :=
  -- Delegate to NumberFieldDeep.lean.
  -- The log bound (log rd_F ≤ C_rd·ℓ·log ℓ, C_rd = 1) is fully proved via `log_two_mul_le`.
  -- The tower data and the Prop-2.2 callback are from the two sorries.
  prop_3_2_to_3_6_via_deep

/-! ## Lemma 2.4: Coset averaging (proved theorem)

The coset averaging argument from the paper: integrate over the quotient
ℂ^f/Λ using the Haar measure and the unfolding trick.  The key identity:
  vol(B_R ∩ (B_R-u)) / vol(B_R) = ρ(R)^f
for unit vectors u, where ρ(R) is the per-coordinate disc-overlap ratio.
Together with |U| ≥ exp(γf) and log ρ(R) > -γ/2, we get that some
coset a+Λ has U-pair density E/|X| ≥ exp(γf/2). -/


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

    From `prop_3_2_to_3_6` (tower data + Prop-2.2 callback) and `prop_p6`
    (analytic γ > 0 lemma), we prove `exists_admissible_family`:
    ∃ γ>0, D>0, ∀ M, ∃ A with A.f ≥ M, A.γ = γ, A.D = D.

    **Proof** (following Proposition 3.8, Steps 1–4 and Remark 3.9):

    Step 1. Choose C_P6 = 4·C_class·C_rd; by `prop_p6` find ℓ₀ such that
            for ℓ = max(ℓ₀, 2): t·log 2 > C_P6·ℓ·log ℓ ≥ log_H_base  (P6 → γ > 0).

    Step 2. `prop_3_2_to_3_6` at ℓ gives D₀, rd_F with log rd_F ≤ C_rd·ℓ·log ℓ.
            Set t = ⌊(ℓ-1)²/200⌋ and log_H_base = 2·C_class·log(2·rd_F).
            Then log_H_base ≤ 4·C_class·C_rd·ℓ·log ℓ (Step 4 of Prop 3.8).

    Step 3. Since t·log 2 − log_H_base > 0 (from P6), the Prop-2.2 callback
            produces U satisfying all AdmissibleFamily fields.

    Step 4. Package as AdmissibleFamily with γ = γ₀ := t·log 2 − log_H_base
            and D = D₀.  These are independent of j (Remark 3.9). -/
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
  -- Step 4: Tower data at ℓ (includes Prop-2.2 callback)
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
  obtain ⟨f, hf_ge, hf1, Λ, hΛ_countable, F, hF_fund, hF_fin, hΛ_sep, hU_callback⟩ := h_levels M
  -- Use the Prop-2.2 callback to get U (requires the CM field K_j)
  obtain ⟨U, hU_mod, hU_in_Λ, hU_size⟩ :=
    hU_callback t log_H_base ht_nonneg hγ_pos
  -- Rewrite hU_size in terms of γ₀
  have hU_size' : (U.card : ℝ) ≥ Real.exp (γ₀ * (f : ℝ)) := by
    have : γ₀ = t * Real.log 2 - log_H_base := rfl
    linarith [hU_size]
  -- Coset averaging via Lemma 2.4
  have hcovg' : ∀ R : ℝ, R > 1/2 → Real.log (rho R) > -(γ₀ / 2) →
      CosetAvgWitness f Λ U R γ₀ := by
    intro R hR hρ
    have hδ_pos : D₀⁻¹ > 0 := inv_pos.mpr hD₀_pos
    exact lemma_2_4 f hf1 Λ hΛ_countable F hF_fund hF_fin D₀⁻¹ hδ_pos hΛ_sep U hU_mod
      hU_in_Λ γ₀ hγ_pos hU_size' R hR hρ
  exact ⟨⟨f, hf1, D₀, hD₀_pos, γ₀, hγ_pos, Λ, U,
      hU_mod, hU_in_Λ, hU_size', hΛ_sep, hcovg'⟩,
    hf_ge, rfl, rfl⟩
