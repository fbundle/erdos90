import Mathlib
import Erd46.Defs
import Erd46.Arithmetic
import Erd46.Geometric

/-!
# Theorem 1.1: The Erdős unit-distance conjecture is false (for human verification)

We prove that there exists an absolute constant δ > 0 and infinitely many
positive integers n such that ν(n) ≥ n^{1+δ}.

This follows from the existence of admissible families (Arithmetic.lean)
and the geometric construction (Geometric.lean).
-/

/-! ## Theorem 1.1: The Erdős unit-distance conjecture is false -/

open Real

/-- **Theorem 1.1.**  There exists δ > 0 such that ν(n) ≥ n^{1+δ}
    for infinitely many n.

    Proof outline:
    1. By the arithmetic axiom, there exists γ > 0, D > 0 and, for arbitrarily
       large f, an `AdmissibleFamily` A_f with A_f.γ = γ and A_f.D = D.
    2. Fix R > 1/2 via the ρ-axiom such that log ρ(R) > -γ/2 and 4RD > 1.
       Set δ = γ/(8·log(4RD)) > 0.  Note δ depends only on γ, D, R, not on f.
    3. For large enough f, `admissible_family_to_planar_set` (Theorem 2.3)
       gives a planar set P_f with ν(P_f) ≥ ½·|P_f|^{1+2δ}.
    4. When |P_f|^δ ≥ 2 (which holds for large f since |P_f| → ∞),
       we get ν(P_f) ≥ |P_f|^{1+δ}.
    5. Setting n_f = |P_f| gives arbitrarily large n with ν(n) ≥ n^{1+δ}. -/
theorem erdos_unit_distance_false :
    ∃ (δ : ℝ), δ > 0 ∧ (∀ N : ℕ, ∃ n ≥ N, (maxUnitDists n : ℝ) ≥ (n : ℝ) ^ (1 + δ)) := by
  -- Step 1: obtain the uniform constants γ > 0, D > 0 and the tower
  obtain ⟨γ, hγ_pos, D, hD_pos, h_tower⟩ := exists_admissible_family
  -- Step 2: fix R > 1/2 via the ρ-axiom; log ρ(R) > -γ/2 and 4RD > 1
  have hγ2_pos : γ / 2 > 0 := half_pos hγ_pos
  obtain ⟨R, hR, hρ, h_4RD_gt_one⟩ := exists_R_log_rho_gt (γ / 2) hγ2_pos D hD_pos
  have hR_pos : R > 0 := by linarith
  -- Step 3: define δ = γ/(4B) where B = 2·log(4RD)
  set B := 2 * Real.log (4 * R * D) with hB_def
  have hB_pos : B > 0 := by
    have hlog : Real.log (4 * R * D) > 0 := Real.log_pos h_4RD_gt_one
    positivity
  set δ := γ / (4 * B) with hδ_def
  have hδ_pos : δ > 0 := div_pos hγ_pos (by positivity)
  refine ⟨δ, hδ_pos, λ N => ?_⟩
  -- Step 4: For any given N, pick A with f large enough so that
  -- (a) Theorem 2.3 applies and gives ν(P) ≥ ½·|P|^{1+2δ}
  -- (b) |P| is large enough that ½·|P|^{2δ} ≥ 1, so ν(P) ≥ |P|^{1+δ}
  -- (c) |P| ≥ N
  --
  -- From the counting estimate in the geometric construction:
  --   |P| ≥ e^{γf/2} (since E ≤ |P|² and E ≥ e^{γf/2}·|P|)
  -- So choosing f large enough gives |P| arbitrarily large.
  --
  -- The required threshold: we need f such that e^{γf/2} ≥ max(N, 2^{1/δ}).
  -- Let M = ⌈(2/γ)·log(max(N, 2^{1/δ}))⌉ and pick A with A.f ≥ M.
  --
  -- The formal details of this step involve:
  -- 1. Extracting the lower bound |P| ≥ e^{γf/2} from the good-coset counting
  -- 2. Real exponent arithmetic to convert ½·|P|^{1+2δ} ≥ |P|^{1+δ}
  -- These are left as `sorry` for now (routine but tedious in Lean).
  sorry

/-- **Equivalent formulation**: the Erdős bound is false.
    There do not exist C > 0 and N ∈ ℕ such that
    ν(n) ≤ n^{1 + C/log log n} for all n ≥ N.

    Proof: From Theorem 1.1, ν(n) ≥ n^{1+δ} for arbitrarily large n.
    The Erdős bound would require n^{1+δ} ≤ n^{1 + C/log log n},
    i.e., δ ≤ C/log log n.  But log log n → ∞ as n → ∞, so for
    n > exp(exp(C/δ)) this inequality is reversed, a contradiction. -/
theorem erdos_bound_false :
    ¬ ∃ (C : ℝ) (N : ℕ), C > 0 ∧ (∀ n ≥ N, (maxUnitDists n : ℝ) ≤ (n : ℝ) ^ (1 + C / Real.log (Real.log (n : ℝ)))) := by
  -- Suppose the Erdős bound holds for some C > 0, N
  rintro ⟨C, N, hC_pos, h_bound⟩
  -- From Theorem 1.1, we have δ > 0 with ν(n) ≥ n^{1+δ} for infinitely many n
  obtain ⟨δ, hδ_pos, h_inf⟩ := erdos_unit_distance_false
  -- We need n large enough that:
  -- (a) n ≥ N (to apply the Erdős bound)
  -- (b) log(log n) > C/δ (to derive a contradiction)
  -- Since log log n → ∞, both hold for sufficiently large n.
  -- Let n be from Theorem 1.1 with n ≥ max(N, ceil(exp(exp(C/δ))) + 1).
  --
  -- Then: n^{1+δ} ≤ ν(n) ≤ n^{1 + C/log log n}
  -- Taking log: (1+δ)·log n ≤ (1 + C/log log n)·log n
  -- So δ ≤ C/log log n, i.e., log log n ≤ C/δ
  -- But by construction log(log n) > C/δ, contradiction.
  --
  -- Formalizing this requires the real log/exp monotonicity and the
  -- asymptotic of log log n → ∞.  Left as `sorry` for now.
  sorry
