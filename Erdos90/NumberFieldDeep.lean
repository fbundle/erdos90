import Mathlib
import Erdos90.Defs
import Erdos90.Arithmetic

open Real Filter NumberField Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal Topology Complex Pointwise

noncomputable section

/-!
# Deep Number-Theoretic Components

This file factors the proof of `prop_3_2_to_3_6` and `prop_2_2` from
`NumberField.lean` into:

1. **Provable helpers** — pure analysis and combinatorics, no sorry.
2. **Golod–Shafarevich tower** — one targeted sorry for the pro-3 tower
   (Props 3.2–3.6: Golod–Shafarevich + Chebotarev + type bridge).
3. **CM norm-one elements** — one targeted sorry for the class-group
   pigeonhole over `ClassGroup K` (Prop 2.2), with corrected hypotheses
   that now include the tower's `D₀` and `rd_F` (since U is constructed
   from the tower's specific CM field K_j, not from an abstract lattice).
4. **Assembly** — the fully proved part that chains the tower, prop_p6
   (analytic γ > 0 lemma), and prop_2_2 together.

The two sorries correspond to the number-theoretic core of [OpenAI 2026]:
- Section 3 (Props 3.2–3.6): producing the tower of CM fields
- Section 2 (Prop 2.2): producing norm-one elements from class-group pigeonhole
-/

/-! ## §1  Analytic helpers (all proved) -/

/-- For ℓ ≥ 2, log(2ℓ) ≤ ℓ · log ℓ. -/
lemma log_two_mul_le (ℓ : ℕ) (hℓ : ℓ ≥ 2) :
    Real.log (2 * (ℓ : ℝ)) ≤ (ℓ : ℝ) * Real.log (ℓ : ℝ) := by
  have hℓ_pos : (0 : ℝ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hℓ_ge2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hlogℓ_ge_log2 : Real.log 2 ≤ Real.log ℓ :=
    Real.log_le_log (by norm_num) hℓ_ge2
  have hlogℓ_pos : Real.log ℓ > 0 :=
    lt_of_lt_of_le (Real.log_pos (by norm_num)) hlogℓ_ge_log2
  rw [Real.log_mul (by norm_num) hℓ_pos.ne']
  have hℓ1_ge1 : (ℓ : ℝ) - 1 ≥ 1 := by linarith
  have hlog2_le : Real.log 2 ≤ (ℓ - 1) * Real.log ℓ :=
    calc Real.log 2 ≤ Real.log ℓ := hlogℓ_ge_log2
      _ = 1 * Real.log ℓ := (one_mul _).symm
      _ ≤ (ℓ - 1) * Real.log ℓ := by nlinarith
  linarith

/-- For ℓ ≥ 2, 2 * ℓ ≥ 1 (used to satisfy rd_F ≥ 1). -/
lemma two_mul_nat_ge_one (ℓ : ℕ) (hℓ : ℓ ≥ 2) : (1 : ℝ) ≤ 2 * (ℓ : ℝ) := by
  have : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  linarith

/-! ## §2  Golod–Shafarevich tower with Chebotarev split primes

**Mathematical content** (Props 3.2–3.6 of [OpenAI 2026]):

Step 1. Choose ℓ primes r₁,…,rₗ ≡ 1 (mod 3).  The cyclic cubic field
F (subfield of ℚ(ζ_{r₁})⋯ℚ(ζ_{rₗ})) has |D_F| = D² = (∏ rᵢ)², M/F
everywhere unramified, d(G) ≥ ℓ−1 for G = Gal(F^{ur,3}/F).

Step 2. By Chebotarev (Prop 3.6), find t = ⌊(ℓ−1)²/100⌋ primes q₁,…,qₜ
with Frobenius in Φ(G).  Set D₀ = Q² where Q = ∏ qᵦ.

Step 3. Golod–Shafarevich: G̅ is infinite (r(G̅) < d(G̅)²/4 for large ℓ),
giving infinite tower F = F₀ ⊂ F₁ ⊂ ⋯ with fⱼ = [Fⱼ : ℚ] → ∞, Kⱼ = Fⱼ(i),
rd(Kⱼ) = rd(F) = |D_F|^{1/3}.

Step 4. For each Kⱼ, the Minkowski embedding Φⱼ : Kⱼ →+* mixedSpace Kⱼ
gives lattice Λⱼ = Φⱼ(D₀⁻¹ · O_{Kⱼ}) ⊂ mixedSpace Kⱼ (≈ ℂ^{fⱼ} for the
totally complex field Kⱼ).  Mathlib provides `fundamentalDomain_integerLattice`
and `volume_fundamentalDomain_latticeBasis`.  The first-coordinate separation
`‖v(fin0)‖ ≥ D₀⁻¹` follows from |N(β)| ≥ 1 and the product formula.

**Lean gaps** (three sub-steps, none in Mathlib v4.29.1):
(a) Golod–Shafarevich: pro-3 group theory, Frattini subgroup, relation-rank
    estimate r ≤ d²/4 (not in Mathlib)
(b) Quantitative Chebotarev: ∃ t primes with prescribed Frobenius (not in Mathlib)
(c) Type bridge: `mixedSpace Kⱼ ≃ Fin fⱼ → ℂ` for totally complex Kⱼ, and
    transport of `integerLattice Kⱼ` + `IsAddFundamentalDomain` across it
    (the isomorphism is in principle constructible via `Fintype.equivFin` +
    `LinearEquiv.piCongrLeft` but the API to use it is missing from Mathlib)
-/

/-- **Golod–Shafarevich tower** (Props 3.2–3.6, sorry'd).

    For each ℓ ≥ 2, produces:
    - `D₀ > 0`  (denominator Q² from the t split primes q₁,…,qₜ)
    - `rd_F ≥ 1`  (root discriminant of the base cubic field F)
    - `log rd_F ≤ ℓ · log ℓ`  (since rd_F ≤ 2ℓ)

    And for every M, a tower level with `f ≥ M`:
    - `Λ ⊂ ℂ^f`  (Minkowski lattice Φⱼ(D₀⁻¹ · O_{Kⱼ}))
    - `F : Set (Fin f → ℂ)`  (fundamental domain of Λ)
    - `IsAddFundamentalDomain Λ F volume`  (Mathlib provides this for number fields)
    - `volume F < ∞`  (Mathlib provides this via `volume_fundamentalDomain_latticeBasis`)
    - `∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf1)‖ ≥ D₀⁻¹`  (first-coordinate separation)

    The tower data (D₀, rd_F, Λ, separation) is the input to `prop_2_2` which
    constructs the norm-one set U via the class-group pigeonhole. -/
def golod_shafarevich_tower_with_lattice :
    ∀ (ℓ : ℕ), ℓ ≥ 2 →
    ∃ (D₀ : ℝ), D₀ > 0 ∧ ∃ (rd_F : ℝ), rd_F ≥ 1 ∧
      Real.log rd_F ≤ (ℓ : ℝ) * Real.log (ℓ : ℝ) ∧
      ∀ (M : ℕ),
        ∃ (f : ℕ), f ≥ M ∧
        ∃ (hf1 : f ≥ 1) (Λ : AddSubgroup (Fin f → ℂ))
          (_ : Countable Λ) (F : Set (Fin f → ℂ)),
          IsAddFundamentalDomain Λ F volume ∧ volume F < ∞ ∧
          (∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf1)‖ ≥ D₀⁻¹) := by
  intro ℓ hℓ
  -- D₀ = Q² (product of split primes squared).  rd_F = |D_F|^{1/3} ≤ 2ℓ.
  -- For each M, the Minkowski lattice Λ of Kⱼ for some j with fⱼ ≥ M.
  -- The sorried sub-steps: Golod–Shafarevich (a), Chebotarev (b), type bridge (c).
  sorry

/-! ## §3  CM norm-one element construction (class-group pigeonhole)

**Mathematical content** (Prop 2.2 of [OpenAI 2026]):

Given the tower data at level j (CM field Kⱼ of degree 2fⱼ, split primes
q₁,…,qₜ, denominator D₀ = Q²):
1. Each q_b gives fⱼ conjugate prime pairs {𝔓_s, c𝔓_s} in O_{Kⱼ}.
2. For ε ∈ {0,1}^m (m = t·fⱼ), form 𝔄_ε = ∏_{εₛ=1} 𝔓_s · ∏_{εₛ=0} c𝔓_s.
3. The 2^m ideals lie in ≤ h(Kⱼ) ≤ H_ℓ^{fⱼ} ideal classes (Prop 3.7).
4. Pigeonhole: ∃ class with ≥ 2^m / H_ℓ^{fⱼ} = exp(γ_ℓ · fⱼ) ideals.
5. For ε, η in the same class, u_ε = α_ε / c(α_ε) gives norm-one elements.
   These form U ⊂ D₀⁻¹ · O_{Kⱼ} ⊂ Λ with |U| ≥ exp(γ_ℓ · fⱼ).

**Hypotheses of this Lean def**:
- `f`, `hf1`, `D₀`, `hD₀`, `Λ`, `hΛ_sep`: tower level data from §2
- `rd_F`: root discriminant of the base field (from §2, to compute log_H)
- `t`, `log_H`: the tower parameters where γ := t·log 2 − log_H > 0
  (t = ⌊(ℓ-1)²/200⌋ determined by ℓ; log_H = 2·C_class·log(2·rd_F))
- `hγ_pos`: proof that γ > 0 (obtained from the analytic `prop_p6` lemma)

Contrast with the old `prop_2_2` signature: the old version took only abstract
`Λ` and `hΛ_sep`, which was insufficient because U depends on the specific CM
field Kⱼ (not just any lattice).  The new signature adds `D₀` and `rd_F` to
document the connection to the tower, and `t`, `log_H`, `γ` to make the
class-group pigeonhole bound explicit.

**Lean gap**: all five steps above require:
(a) CM split-prime ideal pairs in O_{Kⱼ} (not in Mathlib 2025)
(b) The map ε ↦ [𝔄_ε] ∈ ClassGroup Kⱼ and its cardinality estimate
    (`Fintype.exists_ne_map_eq_of_card_lt` is available but needs the map)
(c) The norm-1 quotient αε/c(αε) and the verification |σ(uε)| = 1 for all σ
(d) Lifting u_ε into `AddSubgroup (Fin f → ℂ)` via the type bridge from §2
-/

/-- **CM norm-one elements** (Prop 2.2, sorry'd).

    Constructs the norm-one set U from the tower's CM field Kⱼ via the
    class-group pigeonhole.  All hypotheses come from the tower data (§2)
    and the analytic γ > 0 lemma (prop_p6 in NumberField.lean). -/
def cm_norm_one_elements
    (f : ℕ) (hf1 : f ≥ 1) (D₀ : ℝ) (hD₀ : D₀ > 0) (rd_F : ℝ)
    (t log_H : ℝ) (ht : t ≥ 0) (hγ_pos : t * Real.log 2 - log_H > 0)
    (Λ : AddSubgroup (Fin f → ℂ))
    (hΛ_sep : ∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf1)‖ ≥ D₀⁻¹) :
    ∃ (U : Finset (Fin f → ℂ)),
      (∀ u ∈ U, ∀ r : Fin f, ‖u r‖ = 1) ∧
      (∀ u ∈ U, (u : Fin f → ℂ) ∈ Λ) ∧
      ((U.card : ℝ) ≥ Real.exp ((t * Real.log 2 - log_H) * (f : ℝ))) := by
  -- The proof constructs the 2^{t·f} binary vectors ε, maps each to an ideal
  -- class [𝔄_ε] ∈ ClassGroup Kⱼ, applies `Fintype.exists_ne_map_eq_of_card_lt`
  -- with the bound |ClassGroup Kⱼ| ≤ exp(log_H · f), extracts ≥ exp(γ·f)
  -- elements in one class, and forms u_ε = α_ε / c(α_ε).
  -- All steps require CM field / split-prime ideal API not in Mathlib (2025).
  sorry

/-! ## §4  Assembly of `prop_3_2_to_3_6` -/

/-- **Structured proof of `prop_3_2_to_3_6`** (assembly only; no new sorry).

    Chains `golod_shafarevich_tower_with_lattice` (§2, one sorry) and
    `cm_norm_one_elements` (§3, one sorry) together.  The log bound
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
        IsAddFundamentalDomain Λ F volume ∧ volume F < ∞ ∧
        (∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf1)‖ ≥ D₀⁻¹) ∧
        ∀ (t log_H : ℝ), t ≥ 0 → (t * Real.log 2 - log_H > 0) →
        ∃ (U : Finset (Fin f → ℂ)),
          (∀ u ∈ U, ∀ r : Fin f, ‖u r‖ = 1) ∧
          (∀ u ∈ U, (u : Fin f → ℂ) ∈ Λ) ∧
          ((U.card : ℝ) ≥ Real.exp ((t * Real.log 2 - log_H) * (f : ℝ))) := by
  refine ⟨1, one_pos, fun ℓ hℓ => ?_⟩
  obtain ⟨D₀, hD₀_pos, rd_F, hrd_ge1, hlog_rd, h_levels⟩ :=
    golod_shafarevich_tower_with_lattice ℓ hℓ
  refine ⟨D₀, hD₀_pos, rd_F, hrd_ge1, by linarith, fun M => ?_⟩
  obtain ⟨f, hf_ge, hf1, Λ, hΛ_countable, F, hF_fund, hF_fin, hΛ_sep⟩ := h_levels M
  refine ⟨f, hf_ge, hf1, Λ, hΛ_countable, F, hF_fund, hF_fin, hΛ_sep, fun t log_H ht hγ_pos => ?_⟩
  exact cm_norm_one_elements f hf1 D₀ hD₀_pos rd_F t log_H ht hγ_pos Λ hΛ_sep

end
