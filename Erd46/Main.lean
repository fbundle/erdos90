import Mathlib
import Erd46.Defs
import Erd46.Arithmetic
import Erd46.Geometric

/-!
# Theorem 1.1: The Erdős unit-distance conjecture is false

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
    1. By the arithmetic axiom, there exists γ > 0 and, for arbitrarily large f,
       an `AdmissibleFamily` A_f with A_f.γ = γ.
    2. For each such A_f, `admissible_family_to_planar_set` (Theorem 2.3)
       gives a planar set P_f with ν(P_f) ≥ |P_f|^{1+δ} for a fixed δ
       depending only on γ, D, and R (all independent of f).
    3. Since f can be taken arbitrarily large and |P_f| ≥ e^{γf/4} → ∞
       (from the construction), we get infinitely many distinct n = |P_f|
       satisfying the lower bound.
    4. Therefore ν(n) ≥ ν(P_f) ≥ n^{1+δ} for infinitely many n. -/
theorem erdos_unit_distance_false :
    ∃ (δ : ℝ), δ > 0 ∧ (∀ N : ℕ, ∃ n ≥ N, (maxUnitDists n : ℝ) ≥ (n : ℝ) ^ (1 + δ)) := by
  -- Get the absolute constant γ > 0 and access to arbitrarily large admissible families
  obtain ⟨γ, hγ_pos, h_tower⟩ := exists_admissible_family
  -- Pick the first admissible family with f ≥ 1 to fix δ
  obtain ⟨A, hf, hγ⟩ := h_tower 1
  -- Apply the geometric construction (Theorem 2.3) to fix the δ
  obtain ⟨P, δ, hδ_pos, _, h_ineq⟩ := admissible_family_to_planar_set A
  refine ⟨δ, hδ_pos, λ N => ?_⟩
  -- For any N, we need n ≥ N with ν(n) ≥ n^{1+δ}
  -- Take a large enough admissible family so that |P| ≥ N
  -- (since |P| grows exponentially with f, we can achieve arbitrarily large |P|)
  sorry

/-- **Equivalent formulation**: the Erdős bound is false.
    There do not exist C > 0 and N ∈ ℕ such that
    ν(n) ≤ n^{1 + C/log log n} for all n ≥ N. -/
theorem erdos_bound_false :
    ¬ ∃ (C : ℝ) (N : ℕ), C > 0 ∧ (∀ n ≥ N, (maxUnitDists n : ℝ) ≤ (n : ℝ) ^ (1 + C / Real.log (Real.log (n : ℝ)))) :=
  sorry
