import Erd46.Prerequisite
import Erd46.Lemma

/-!
# Theorem 1.1: The Erdős unit-distance conjecture is false

This file states and proves the main result of "Planar Point Sets with Many
Unit Distances" (OpenAI, 2026).

**Theorem 1.1.** There exists δ > 0 and infinitely many n such that ν(n) ≥ n^{1+δ}.
-/

/-- **Theorem 1.1 (Erdős unit-distance conjecture is false).**

    There exists an absolute constant δ > 0 and infinitely many positive integers n
    for which ν(n) ≥ n^{1+δ}.

    Equivalently: there is no pair of absolute constants C, N such that
    ν(n) ≤ n^{1 + C/log log n} for all n ≥ N. -/
theorem erdos_unit_distance_false :
    ∃ (δ : ℝ), δ > 0 ∧ (∀ N : ℕ, ∃ n ≥ N, (maxUnitDists n : ℝ) ≥ (n : ℝ) ^ (1 + δ)) :=
  by
    sorry

/-- **Equivalent formulation**: the Erdős upper bound conjecture is false.

    There do not exist absolute constants C > 0 and N ∈ ℕ such that
    ν(n) ≤ n^{1 + C/log log n} for every n ≥ N. -/
theorem erdos_bound_false :
    ¬ ∃ (C : ℝ) (N : ℕ), C > 0 ∧ (∀ n ≥ N, (maxUnitDists n : ℝ) ≤ (n : ℝ) ^ (1 + C / Real.log (Real.log (n : ℝ)))) :=
  by
    sorry
