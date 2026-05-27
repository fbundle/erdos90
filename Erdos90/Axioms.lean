import Mathlib
import Erdos90.CMField.Basic

open Real Filter NumberField InfinitePlace Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal Topology Complex Pointwise BigOperators

noncomputable section

/-!
# Axioms

This file collects the non-Mathlib axioms in the dependency closure of
`Erdos90.Main.erdos_unit_distance_false`.  On this `master` branch there is
exactly one such axiom: `brd_tower_data`.  All other sorries in the project
are off-path (not depended on by the main theorem).

When the four Mathlib gaps listed in the docstring of `brd_tower_data` close,
this axiom becomes a theorem with no source-code change to downstream callers.
-/

/-- **BRD CM tower data** — bundles the ℓ-level constants and a per-(M, t, log_H)
callable producing a BRD tower level (CM field K of complex degree f ≥ M, with
SplitPrimeData of fixed Q across the tower, and a quantitative class-number
bound). -/
structure BRDTowerData (ℓ : ℕ) where
  Q : ℕ
  hQ_pos : Q > 0
  D₀ : ℝ
  hD₀_pos : D₀ > 0
  hD₀_eq : D₀ = ((Q : ℝ))^2
  rd_F : ℝ
  hrd_F_ge1 : rd_F ≥ 1
  hlog_rd : Real.log rd_F ≤ (ℓ : ℝ) * Real.log (ℓ : ℝ)
  getTowerLevel (M : ℕ) (t log_H : ℝ) (ht : t ≥ 0) (hlog_H_pos : log_H > 0)
      (hlog_H_ge_rd : log_H ≥ 2 * Real.log (2 * rd_F)) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K)
      (_ : IsTotallyComplex K) (f : ℕ) (_ : f ≥ M) (_ : f ≥ 1)
      (_ : InfinitePlace.nrComplexPlaces K = f)
      (_ : InfinitePlace.nrRealPlaces K = 0)
      (t' : ℕ) (_ : t + 1 ≤ (t' : ℝ))
      (sp : SplitPrimeData K (t' * f)),
      sp.Q = Q ∧
      Real.log (Fintype.card (ClassGroup (𝓞 K)) : ℝ) / (f : ℝ) ≤ log_H

/-- **BRD tower data** (HMR 2021 + Friedman/Louboutin Brauer–Siegel, axiom).

Bundles two independent number-theoretic results:

**(1) HMR 2021 — Golod–Shafarevich CM tower with fixed split primes.**

For each `ℓ ≥ 2` there is a root-discriminant bound `rd_F` (with
`log rd_F ≤ ℓ · log ℓ`) and a tower-fixed product `Q : ℕ` of split primes
such that for every `M, t'` there is a CM totally-complex number field `K`
of complex degree `f ≥ M` with `rootDiscr K ≤ rd_F` and a
`SplitPrimeData K (t' · f)` whose `sp.Q = Q`.

Citation:
- Hajir, Maire, Ramakrishna, *Cutting class field theory towers*, 2021.
  ArXiv:2103.05382.  Local copy: `assets/hmr_2021_src/Cutting_towers_arxiv.tex`.
  See §3 `theo:ihara` (Ihara's split-prime persistence in the tower).
- Golod, Shafarevich, *On the class field tower*, Izv. Akad. Nauk SSSR Ser.
  Mat. 28 (1964), 261–272 (existence of infinite class field towers).
- Standard CM lift: tensor the totally-real base field with `ℚ(√-d)` for
  any d with controlled discriminant contribution.

**(2) Friedman–Louboutin quantitative Brauer–Siegel for CM fields.**

For CM totally-complex `K` of complex degree `f` with `rootDiscr K ≤ rd_F`
(`f ≥ 5`),
   `log (h_K) / f ≤ 2 · log (2 · rd_F)`
where `h_K = |Cl(𝓞_K)|`.

Citation:
- Friedman, *Analytic formulas for the regulator of a number field*,
  Inventiones 98 (1989), 599–622.  Lower bound `R_K ≥ 1/5` for CM TC K.
- Louboutin, *Explicit upper bounds for residues of Dedekind zeta functions
  and class numbers of CM-fields*, Math. Comp. 69 (2000), 311–339.  Upper
  bound `Res_{s=1} ζ_K(s) ≤ (4 · rd_F)^f`.
- Brauer, *On the zeta-functions of algebraic number fields*, Amer. J. Math.
  69 (1947), 243–250 (the Brauer–Siegel chain).
- Combined Brauer–Siegel: `log(h_K · R_K) = log |d_K|^{1/2} + O(1)`, see
  Lang *Algebraic Number Theory* Ch. XVI.

## Formalization status

On the `full` branch this axiom is a PROVED Lean assembly modulo four named
on-path sub-postulates that decompose the two results above:
- `gs_cm_tower_infinite_postulate` (Mathlib gap: pro-`p` group + GS inequality
  + HCF construction).
- `chebotarev_fixed_Q` (Mathlib gap: Chebotarev density + L-function
  continuation past `s = 1`).
- `friedman_regulator_lower_bound_postulate` (Mathlib gap: Stark/Tate's
  ζ_K(0) formula + Friedman's integral bound).
- `phragmen_lindelof_zeta_holds_postulate` (Mathlib gap: `dedekindZeta`
  functional equation + Phragmén–Lindelöf + boundary bounds via Stirling).

On this `master` branch, the four sub-postulates are bundled into a single
axiom.  When the four Mathlib gaps close, the axiom becomes a theorem with
no source code change to `brd_cm_tower_postulate` or downstream callers. -/
axiom brd_tower_data (ℓ : ℕ) (hℓ : ℓ ≥ 2) : BRDTowerData ℓ

end
