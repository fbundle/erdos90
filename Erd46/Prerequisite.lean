import Mathlib

open Set
open Real

/-!
# Prerequisites for the Erdős unit-distance conjecture disproof

This file defines the basic notions needed to state Theorem 1.1 of
"Planar Point Sets with Many Unit Distances" (OpenAI, 2026):
the unit-distance counting functions ν(P) and ν(n).
-/

/-- Squared Euclidean distance between two points in ℝ².
    Using squared distance avoids the square root in the unit-distance condition. -/
noncomputable def distSq (p q : ℝ × ℝ) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- `unitDistPairs P` = ν(P): the number of unordered unit-distance pairs
    in a finite planar set P ⊂ ℝ².

    We count each unordered pair {x, y} (x ≠ y) such that |x - y| = 1.
    Since `P.offDiag` contains ordered distinct pairs (x, y), and the distance
    condition is symmetric, the filtered count is always even, so division by 2
    is exact. -/
noncomputable def unitDistPairs (P : Finset (ℝ × ℝ)) : ℕ :=
  ((P.offDiag).filter (λ ⟨x, y⟩ => distSq x y = 1)).card / 2

/-- `maxUnitDists n` = ν(n): the maximum number of unit-distance pairs
    attainable by any n-point planar set.

    For a fixed n, ν(n) is bounded above by n·(n-1)/2 (the total number of
    unordered pairs), so the supremum is finite and well-defined. -/
noncomputable def maxUnitDists (n : ℕ) : ℕ :=
  sSup {k | ∃ (P : Finset (ℝ × ℝ)), P.card = n ∧ unitDistPairs P = k}
