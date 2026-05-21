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
    3. For large enough f, `planar_set_from_datum` gives a planar set P_f with
       - |P_f| ≥ exp(γ/2 · f), so |P_f| → ∞ as f → ∞
       - ν(P_f) ≥ ½ · exp(γ/2 · f) · |P_f| ≥ ½ · |P_f|^{2δ} · |P_f| = ½ · |P_f|^{1+2δ}
         (using |P_f| ≤ exp(B·f) so exp(γ/2·f) ≥ |P_f|^{γ/(2B)} = |P_f|^{2δ})
    4. For |P_f|^δ ≥ 2 (large f), ½ · |P_f|^{1+2δ} ≥ |P_f|^{1+δ}.
    5. Setting n_f = |P_f| gives arbitrarily large n with ν(n) ≥ n^{1+δ}. -/
theorem erdos_unit_distance_false :
    ∃ (δ : ℝ), δ > 0 ∧ (∀ N : ℕ, ∃ n ≥ N, (maxUnitDists n : ℝ) ≥ (n : ℝ) ^ (1 + δ)) := by
  -- Step 1: obtain the uniform constants γ > 0, D > 0 and the tower
  obtain ⟨γ, hγ_pos, D, hD_pos, h_tower⟩ := exists_admissible_family
  -- Step 2: fix R > 1/2 via the ρ-axiom; log ρ(R) > -γ/2 and 4RD > 1
  have hγ2_pos : γ / 2 > 0 := half_pos hγ_pos
  obtain ⟨R, hR, hρ_global, h_4RD_gt_one⟩ := exists_R_log_rho_gt (γ / 2) hγ2_pos D hD_pos
  -- Step 3: define δ = γ/(4B) where B = 2·log(4RD); this is independent of f
  set B := 2 * Real.log (4 * R * D) with hB_def
  have hB_pos : B > 0 := by
    have hlog : Real.log (4 * R * D) > 0 := Real.log_pos h_4RD_gt_one
    positivity
  set δ := γ / (4 * B) with hδ_def
  have hδ_pos : δ > 0 := div_pos hγ_pos (by positivity)
  refine ⟨δ, hδ_pos, fun N => ?_⟩
  -- Step 4: for any N, pick f large enough, get an admissible family A with
  -- A.f ≥ M, A.γ = γ, A.D = D, then apply planar_set_from_datum.
  --
  -- We need f large enough that:
  -- (a) exp(γ/2 · f) ≥ N  (so |P| ≥ N)
  -- (b) exp(γ/2 · f)^δ ≥ 2  (so ½ · |P|^{1+2δ} ≥ |P|^{1+δ})
  --
  -- Both (a) and (b) hold for all sufficiently large f since exp(γ/2 · f) → ∞.
  -- We leave the choice of M and the subsequent quantitative estimates as sorry,
  -- as they require real exp/log monotonicity and rpow arithmetic.
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
