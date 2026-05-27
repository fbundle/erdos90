/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Erdos90.Mathlib4_Extra.NumberTheory.NumberField.Discriminant.UnramifiedDiscriminant

/-!
# Number field invariants — references + simple PROVED corollaries

This file documents and packages the various **invariants** of a number
field `K`:

* `Module.finrank ℚ K` — the degree `[K : ℚ]`.
* `NumberField.classNumber K` — the cardinality of the class group `h_K`.
* `NumberField.Units.regulator K` — the regulator `R_K`.
* `NumberField.Units.torsionOrder K` — `w_K = |μ(K)|`.
* `NumberField.discr K` — the discriminant.
* `NumberField.rootDiscr K` — the root discriminant `|disc K|^{1/[K:ℚ]}`.
* `NumberField.InfinitePlace.nrRealPlaces K`, `nrComplexPlaces K` — embedding type counts.

All of these are PROVED in Mathlib v4.30.

## Asymptotic relations (Dirichlet class number formula)

Mathlib proves the **analytic class number formula** at `s = 1`:

  `Tendsto (fun s ↦ (s - 1) · ζ_K(s)) (𝓝[>] 1) (𝓝 (residue))`

where `residue = 2^{r_1} · (2π)^{r_2} · R_K · h_K / (w_K · √|disc K|)`.

See `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`.

## What's NOT in Mathlib v4.30

- The class number formula at `s = 0` (which gives `R_K · h_K / w_K` directly).
- Functional equation of `dedekindZeta` (would close all 4 proof-path
  sorries indirectly).
- Brauer–Siegel theorem (asymptotic `log(h_K · R_K) / √|disc K|`).

## What this file provides

Documentation + simple PROVED corollaries that aren't in Mathlib but follow
trivially from existing infrastructure.

## References

- Marcus, *Number Fields*, Chapter 6 (class number formula).
- Neukirch, *Algebraic Number Theory*, Chapter VII (analytic CFT).
- Lang, *Algebraic Number Theory*, Chapter VIII.
-/

namespace NumberField

universe u

/-- For ℚ, the root discriminant is exactly 1. -/
theorem rootDiscr_rat_eq_one : rootDiscr ℚ = 1 := NumberField.rootDiscr_rat

/-- `classNumber ℚ = 1` (since `ℤ` is a PID).

PROVED Lean: direct citation of Mathlib's `Rat.classNumber_eq`. -/
theorem classNumber_rat_eq_one : NumberField.classNumber ℚ = 1 :=
  Rat.classNumber_eq

end NumberField
