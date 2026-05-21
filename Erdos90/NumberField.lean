import Mathlib
import Erdos90.Defs
import Erdos90.Arithmetic

open Real Filter NumberField

noncomputable section

/-!
# Section 3: Field Tower Construction (Lean translation)

This file translates the proof of `exists_admissible_family` from the paper
"Planar Point Sets with Many Unit Distances" (OpenAI, 2026) into Lean 4.

The deep number-theoretic steps are declared as `axiom`s, each corresponding
directly to a proposition in the paper. The analytic estimate γ > 0 (Property P6)
is identified as a separate lemma (currently `sorry`-closed, but provable via
`Real.isLittleO_log_id_atTop`: log = o(id) implies ℓ/log ℓ → ∞).

## Sub-axioms declared here

1. `prop_3_2_to_3_6`      — Golod–Shafarevich + Chebotarev tower output
2. `prop_2_2`             — norm-one set construction (class-group pigeonhole)
3. `prop_2_2_covg`        — Haar measure coset averaging (Lemma 2.4)

`C_class` is a concrete `def := 1`. `C₀` and `prop_3_7` are absorbed into the
three axioms above; they are not separately assumed.
These three axioms and the analytic lemmas (prop_p6, hlog2_event) together
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
axiom prop_3_2_to_3_6 :
    ∃ (C_rd : ℝ), C_rd > 0 ∧
    ∀ (ℓ : ℕ), ℓ ≥ 2 →
    ∃ (D₀ : ℝ) (hD₀ : D₀ > 0) (rd_F : ℝ) (_ : rd_F ≥ 1),
      Real.log rd_F ≤ C_rd * (ℓ : ℝ) * Real.log (ℓ : ℝ) ∧
      ∀ (M : ℕ),
      ∃ (f : ℕ) (_ : f ≥ M) (hf1 : f ≥ 1) (Λ : AddSubgroup (Fin f → ℂ)),
        ∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf1)‖ ≥ D₀⁻¹

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

/-- **Proposition 2.2 + Lemma 2.4 (combined).**

    Given:
    - Degree f ≥ 1 and denominator D₀ > 0
    - t ≥ 0 (number of split prime pairs) and log_H (log of the class-number bound base)
    - γ := t·log 2 − log_H > 0 (from Proposition 3.8, Property P6)
    - Minkowski lattice Λ with D₀-separation

    Produces U ⊂ ℂ^f with:
    - All coordinates of u ∈ U have modulus 1   (|σ(u)| = 1 for all embeddings)
    - D₀ · u ∈ Λ for all u ∈ U                 (u ∈ D₀⁻¹ 𝓞_K ↔ D₀·u ∈ 𝓞_K ⊂ Λ)
    - |U| ≥ exp(γ · f)                          (pigeonhole on h(K) ≤ H^f ideal classes)
    - CosetAvgWitness for all suitable R         (Lemma 2.4: Haar measure averaging) -/
-- Prop-valued part: existence of the norm-one set U with size bound.
axiom prop_2_2 (f : ℕ) (hf1 : f ≥ 1) (D₀ : ℝ) (hD₀ : D₀ > 0) (t log_H : ℝ)
    (ht : t ≥ 0) (hγ : t * Real.log 2 - log_H > 0)
    (Λ : AddSubgroup (Fin f → ℂ))
    (hΛ_sep : ∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf1)‖ ≥ D₀⁻¹) :
    ∃ (U : Finset (Fin f → ℂ)),
      (∀ u ∈ U, ∀ r : Fin f, ‖u r‖ = 1) ∧
      (∀ u ∈ U, D₀ • u ∈ Λ) ∧
      ((U.card : ℝ) ≥ Real.exp ((t * Real.log 2 - log_H) * (f : ℝ)))

-- Type-valued part: coset averaging witness (Lemma 2.4).
-- CosetAvgWitness is a Type, not Prop, so this must be a separate axiom/def.
axiom prop_2_2_covg (f : ℕ) (hf1 : f ≥ 1) (D₀ : ℝ) (hD₀ : D₀ > 0) (t log_H : ℝ)
    (ht : t ≥ 0) (hγ : t * Real.log 2 - log_H > 0)
    (Λ : AddSubgroup (Fin f → ℂ))
    (hΛ_sep : ∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf1)‖ ≥ D₀⁻¹)
    (U : Finset (Fin f → ℂ))
    (hU_mod : ∀ u ∈ U, ∀ r : Fin f, ‖u r‖ = 1)
    (hU_in_Λ : ∀ u ∈ U, D₀ • u ∈ Λ)
    (R : ℝ) (hR : R > 1/2)
    (hρ : Real.log (rho R) > -((t * Real.log 2 - log_H) / 2)) :
    CosetAvgWitness f Λ U R (t * Real.log 2 - log_H)

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
  obtain ⟨f, hf_ge, hf1, Λ, hΛ_sep⟩ := h_levels M
  obtain ⟨U, hU_mod, hU_in_Λ, hU_size⟩ :=
    prop_2_2 f hf1 D₀ hD₀_pos t log_H_base ht_nonneg hγ_pos Λ hΛ_sep
  -- Rewrite hU_size in terms of γ₀
  have hU_size' : (U.card : ℝ) ≥ Real.exp (γ₀ * (f : ℝ)) := by
    have : γ₀ = t * Real.log 2 - log_H_base := rfl
    linarith [hU_size]
  -- Coset averaging for all suitable R (uses prop_2_2_covg, Type-valued)
  have hcovg' : ∀ R : ℝ, R > 1/2 → Real.log (rho R) > -(γ₀ / 2) →
      CosetAvgWitness f Λ U R γ₀ := by
    intro R hR hρ
    have heq : (t * Real.log 2 - log_H_base) = γ₀ := rfl
    have hρ' : Real.log (rho R) > -((t * Real.log 2 - log_H_base) / 2) := by linarith
    exact heq ▸ prop_2_2_covg f hf1 D₀ hD₀_pos t log_H_base ht_nonneg hγ_pos Λ hΛ_sep
        U hU_mod hU_in_Λ R hR hρ'
  exact ⟨⟨f, hf1, D₀, hD₀_pos, γ₀, hγ_pos, Λ, U,
      hU_mod, hU_in_Λ, hU_size', hΛ_sep, hcovg'⟩,
    hf_ge, rfl, rfl⟩
