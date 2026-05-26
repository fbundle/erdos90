import Mathlib
import Erdos90.Mathlib4_Extra.Analytic

open Real

noncomputable section

/-!
# Analytic helpers for the Erdős Problem 90 disproof

Pure analytic lemmas used by the Golod–Shafarevich tower construction (§2)
and the class-group pigeonhole bound (§5).  All proved; no sorries.

The three core lemmas (`log_two_mul_le`, `exp_sub_mul_eq_rpow_div_exp`,
`card_ratio_ineq`) are Mathlib candidates and now live in
`Erdos90.Mathlib4_Extra.Analytic`.  This file re-exports them at the top
level for backwards compatibility with existing call sites.
-/

/-! ## §1  Analytic helpers (re-exported from Mathlib4_Extra) -/

export Mathlib4_Extra (log_two_mul_le exp_sub_mul_eq_rpow_div_exp card_ratio_ineq)
