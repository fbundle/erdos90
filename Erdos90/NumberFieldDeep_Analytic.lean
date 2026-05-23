import Mathlib

open Real

noncomputable section

/-!
# Analytic helpers for the Erdős Problem 90 disproof

Pure analytic lemmas used by the Golod–Shafarevich tower construction (§2)
and the class-group pigeonhole bound (§5).  All proved; no sorries.
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

/-- **Key exponential identity for Prop 2.2.**  Relates `exp((t·log 2 − log_H)·f)` to
    `2^{t·f} / exp(log_H·f)`.  This is the analytic core of the class-group pigeonhole bound:
    `2^{t·f} / H^f ≥ exp((t·log 2 − log_H)·f)` because `2^x = exp(x·log 2)`. -/
lemma exp_sub_mul_eq_rpow_div_exp (t log_H : ℝ) (f : ℝ) :
    Real.exp ((t * Real.log 2 - log_H) * f) = ((2 : ℝ) ^ (t * f)) / Real.exp (log_H * f) := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  rw [Real.rpow_def_of_pos h2pos (t * f)]
  calc
    Real.exp ((t * Real.log 2 - log_H) * f)
        = Real.exp ((t * Real.log 2) * f - log_H * f) := by ring_nf
    _ = Real.exp ((t * Real.log 2) * f) / Real.exp (log_H * f) := by rw [Real.exp_sub]
    _ = Real.exp (Real.log (2 : ℝ) * (t * f)) / Real.exp (log_H * f) := by ring_nf

/-- **Cardinality ratio inequality** (for Prop 2.2).  If `|E| ≥ 2^{t·f}` and `|G| ≤ exp(log_H·f)`
    with `|G| > 0`, then `|E|/|G| ≥ exp((t·log 2 − log_H)·f)`.
    This extracts the purely arithmetic part of the fiber-size bound from the class-group
    pigeonhole. -/
lemma card_ratio_ineq (t log_H : ℝ) (f : ℕ) (cardE cardG : ℕ)
    (hGpos : cardG > 0)
    (hE : (2 : ℝ) ^ (t * (f : ℝ)) ≤ (cardE : ℝ))
    (hG : (cardG : ℝ) ≤ Real.exp (log_H * (f : ℝ))) :
    Real.exp ((t * Real.log 2 - log_H) * (f : ℝ)) ≤ (cardE : ℝ) / (cardG : ℝ) := by
  have h_nonneg_cardE : (0 : ℝ) ≤ (cardE : ℝ) := by exact_mod_cast Nat.zero_le _
  have h_pos_cardG : (0 : ℝ) < (cardG : ℝ) := by exact_mod_cast hGpos
  have h_div : ((2 : ℝ) ^ (t * (f : ℝ))) / Real.exp (log_H * (f : ℝ)) ≤
      (cardE : ℝ) / (cardG : ℝ) :=
    div_le_div₀ h_nonneg_cardE hE h_pos_cardG hG
  rw [exp_sub_mul_eq_rpow_div_exp t log_H (f : ℝ)]
  exact h_div
