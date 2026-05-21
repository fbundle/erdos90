import Mathlib

open Real

/-!
# Definitions (for human verification)

ν(P) = number of unordered unit-distance pairs in a finite planar set P ⊂ ℝ²,
ν(n) = max_{|P|=n} ν(P).

These are the core objects of the unit-distance problem, as defined in
"Planar Point Sets with Many Unit Distances" (OpenAI, 2026).
-/

/-- Squared Euclidean distance in ℝ².  |x-y| = 1 ↔ distSq x y = 1. -/
noncomputable def distSq (p q : ℝ × ℝ) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- ν(P): number of unordered unit-distance pairs in P.
    `P.offDiag` gives ordered distinct pairs; the distance condition is symmetric,
    so the filtered count is always even, making division by 2 exact. -/
noncomputable def unitDistPairs (P : Finset (ℝ × ℝ)) : ℕ :=
  ((P.offDiag).filter (λ ⟨x, y⟩ => distSq x y = 1)).card / 2

/-- ν(n): maximum number of unit-distance pairs attainable by an n-point planar set. -/
noncomputable def maxUnitDists (n : ℕ) : ℕ :=
  sSup {k | ∃ (P : Finset (ℝ × ℝ)), P.card = n ∧ unitDistPairs P = k}
