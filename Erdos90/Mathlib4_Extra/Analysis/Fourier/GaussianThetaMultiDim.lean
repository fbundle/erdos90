/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Mathlib
import Erdos90.Mathlib4_Extra.Analysis.Fourier.PoissonProd

/-!
# Multi-dimensional Jacobi theta modular transformation (Step B)

For `d : ℕ` and `Re(a) > 0`,
  `∑' n : Fin d → ℤ, cexp(-π·a·∑_i (n i)²) = a^(-d/2) · ∑' n : Fin d → ℤ, cexp(-π/a·∑_i (n i)²)`.

This is Step B in the roadmap toward the Dedekind zeta functional equation
(via the lattice theta function for CM fields).  The route is **iterative**
rather than going through a d-D Schwartz Poisson construction: we use the
1-D theta identity `Complex.tsum_exp_neg_mul_int_sq` and induct on `d`
using `Fin.consEquiv` to split `(Fin (d+1) → ℤ) ≃ ℤ × (Fin d → ℤ)`.

This mirrors the Step A approach (2-D via product factorization, in
`PoissonProd.lean`).  No 2-D or d-D Schwartz Gaussian construction is needed.
-/

open Complex Real

namespace SchwartzMap

/-- The d-D Gaussian sum `∑' n : Fin d → ℤ, cexp(-π·a·∑_i (n i)²)`. -/
noncomputable def gaussianThetaMultiDim (d : ℕ) (a : ℂ) : ℂ :=
  ∑' n : Fin d → ℤ, Complex.exp (-Real.pi * a * ∑ i, (n i : ℂ) ^ 2)

/-- Factorization: `cexp(-π·a·∑_i (n i)²) = ∏_i cexp(-π·a·(n i)²)`. -/
theorem cexp_neg_pi_mul_finset_sum_sq (d : ℕ) (a : ℂ) (n : Fin d → ℂ) :
    Complex.exp (-Real.pi * a * ∑ i, n i ^ 2) =
      ∏ i, Complex.exp (-Real.pi * a * n i ^ 2) := by
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]

/-- Summability of `n ↦ cexp(-π·a·∑_i (n i)²)` over `Fin d → ℤ` for `Re(a) > 0`.
Proved by induction on `d`, using `Fin.consEquiv` to split the index set. -/
theorem summable_cexp_neg_pi_mul_finset_sum_sq :
    ∀ (d : ℕ) {a : ℂ}, 0 < a.re →
      Summable (fun n : Fin d → ℤ =>
        Complex.exp (-Real.pi * a * ∑ i, (n i : ℂ) ^ 2)) := by
  intro d
  induction d with
  | zero =>
    intro a _
    -- Fin 0 → ℤ has only one element (the empty function).
    -- The function is constant cexp(-π·a·0) = cexp(0) = 1; summable trivially.
    refine summable_of_finite_support ?_
    apply Set.Finite.subset (Set.finite_univ : (Set.univ : Set (Fin 0 → ℤ)).Finite)
    intro _ _; trivial
  | succ d IH =>
    intro a ha
    -- Use Fin.consEquiv to split (Fin (d+1) → ℤ) ≃ ℤ × (Fin d → ℤ).
    -- ∑' n : Fin (d+1) → ℤ, cexp(-π·a·∑_i (n i)²)
    -- = ∑' (z : ℤ, n' : Fin d → ℤ), cexp(-π·a·(z² + ∑_i (n' i)²))
    -- = ∑' (z, n'), cexp(-π·a·z²) · cexp(-π·a·∑_i (n' i)²)  (factorization)
    -- = (∑' z, cexp(-π·a·z²)) · (∑' n', cexp(-π·a·∑_i (n' i)²))  (tsum_mul_tsum)
    -- The product summability + IH yields the result.
    have h_1d := summable_cexp_neg_pi_mul_int_sq ha
    have h_norm_1d := summable_norm_cexp_neg_pi_mul_int_sq ha
    have h_d_summ := IH ha
    -- The equivalence (ℤ × (Fin d → ℤ)) ≃ (Fin (d+1) → ℤ)
    let e : ℤ × (Fin d → ℤ) ≃ (Fin (d + 1) → ℤ) :=
      Fin.consEquiv (fun _ => ℤ)
    -- Function in the (Fin (d+1) → ℤ) form.
    set F : (Fin (d + 1) → ℤ) → ℂ :=
      fun n => Complex.exp (-Real.pi * a * ∑ i, (n i : ℂ) ^ 2) with hF_def
    -- Pulling back via e: F (e (z, n')) = cexp(-π·a·(z² + ∑_i (n' i : ℂ)²))
    --                                   = cexp(-π·a·z²) · cexp(-π·a·∑_i (n' i)²)
    have h_e_apply : ∀ (z : ℤ) (n' : Fin d → ℤ),
        F (e (z, n')) =
          Complex.exp (-Real.pi * a * (z : ℂ) ^ 2) *
          Complex.exp (-Real.pi * a * ∑ i, (n' i : ℂ) ^ 2) := by
      intro z n'
      simp only [F, e, Fin.consEquiv, Equiv.coe_fn_mk]
      rw [show (∑ i, ((Fin.cons z n' : Fin (d + 1) → ℤ) i : ℂ) ^ 2) =
              (z : ℂ) ^ 2 + ∑ i, (n' i : ℂ) ^ 2 from ?_]
      · rw [← Complex.exp_add]; congr 1; ring
      · rw [Fin.sum_univ_succ]
        simp [Fin.cons_zero, Fin.cons_succ]
    -- Summability of (z, n') ↦ cexp(-π·a·z²) · cexp(-π·a·∑_i (n' i)²)
    -- via Summable.mul_of_nonneg on norms + Summable.of_norm_bounded_eventually.
    have h_prod_norm_summ : Summable (fun p : ℤ × (Fin d → ℤ) =>
        ‖Complex.exp (-Real.pi * a * (p.1 : ℂ) ^ 2)‖ *
        ‖Complex.exp (-Real.pi * a * ∑ i, (p.2 i : ℂ) ^ 2)‖) :=
      Summable.mul_of_nonneg h_norm_1d h_d_summ.norm
        (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    have h_prod_summ : Summable (fun p : ℤ × (Fin d → ℤ) =>
        Complex.exp (-Real.pi * a * (p.1 : ℂ) ^ 2) *
        Complex.exp (-Real.pi * a * ∑ i, (p.2 i : ℂ) ^ 2)) := by
      refine h_prod_norm_summ.of_norm_bounded_eventually (g := fun p =>
          ‖Complex.exp (-Real.pi * a * (p.1 : ℂ) ^ 2)‖ *
          ‖Complex.exp (-Real.pi * a * ∑ i, (p.2 i : ℂ) ^ 2)‖) ?_
      refine Filter.Eventually.of_forall (fun p => ?_)
      rw [norm_mul]
    -- Transport summability via the equivalence e.
    have h_F_e : Summable (fun p : ℤ × (Fin d → ℤ) => F (e p)) := by
      refine h_prod_summ.congr (fun p => ?_)
      exact (h_e_apply p.1 p.2).symm
    exact e.summable_iff.mp h_F_e

/-- The 1-D Gaussian sum `theta1 a := ∑' n : ℤ, cexp(-π·a·n²)`. -/
noncomputable def theta1 (a : ℂ) : ℂ :=
  ∑' n : ℤ, Complex.exp (-Real.pi * a * (n : ℂ) ^ 2)

/-- The d-D Gaussian theta equals the d-th power of the 1-D theta. -/
theorem gaussianThetaMultiDim_eq_theta1_pow :
    ∀ (d : ℕ) {a : ℂ}, 0 < a.re →
      gaussianThetaMultiDim d a = (theta1 a) ^ d := by
  intro d
  induction d with
  | zero =>
    intro a _
    -- ∑' n : Fin 0 → ℤ, cexp(0) = cexp(0) · |Fin 0 → ℤ| = 1; (theta1 a)^0 = 1.
    unfold gaussianThetaMultiDim
    have h_one : ∀ n : Fin 0 → ℤ,
        Complex.exp (-Real.pi * a * ∑ i, (n i : ℂ) ^ 2) = 1 := by
      intro n
      have h_sum : (∑ i : Fin 0, (n i : ℂ) ^ 2) = 0 := by simp
      rw [h_sum]; simp
    rw [tsum_congr h_one, tsum_const, pow_zero]
    simp
  | succ d IH =>
    intro a ha
    -- Factor: ∑' n : Fin (d+1) → ℤ, ... = ∑' (z, n') : ℤ × (Fin d → ℤ), ...
    --                                   = (∑' z, cexp(-π·a·z²)) · gaussianThetaMultiDim d a.
    have h_1d := summable_cexp_neg_pi_mul_int_sq ha
    have h_norm_1d := summable_norm_cexp_neg_pi_mul_int_sq ha
    have h_d_summ := summable_cexp_neg_pi_mul_finset_sum_sq d ha
    let e : ℤ × (Fin d → ℤ) ≃ (Fin (d + 1) → ℤ) :=
      Fin.consEquiv (fun _ => ℤ)
    have h_e_apply : ∀ (z : ℤ) (n' : Fin d → ℤ),
        Complex.exp (-Real.pi * a * ∑ i, ((e (z, n')) i : ℂ) ^ 2) =
          Complex.exp (-Real.pi * a * (z : ℂ) ^ 2) *
          Complex.exp (-Real.pi * a * ∑ i, (n' i : ℂ) ^ 2) := by
      intro z n'
      simp only [e, Fin.consEquiv, Equiv.coe_fn_mk]
      rw [show (∑ i, ((Fin.cons z n' : Fin (d + 1) → ℤ) i : ℂ) ^ 2) =
              (z : ℂ) ^ 2 + ∑ i, (n' i : ℂ) ^ 2 from ?_]
      · rw [← Complex.exp_add]; congr 1; ring
      · rw [Fin.sum_univ_succ]
        simp [Fin.cons_zero, Fin.cons_succ]
    -- Product summability for the (z, n') space.
    have h_prod_norm_summ : Summable (fun p : ℤ × (Fin d → ℤ) =>
        ‖Complex.exp (-Real.pi * a * (p.1 : ℂ) ^ 2)‖ *
        ‖Complex.exp (-Real.pi * a * ∑ i, (p.2 i : ℂ) ^ 2)‖) :=
      Summable.mul_of_nonneg h_norm_1d h_d_summ.norm
        (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    have h_prod_summ : Summable (fun p : ℤ × (Fin d → ℤ) =>
        Complex.exp (-Real.pi * a * (p.1 : ℂ) ^ 2) *
        Complex.exp (-Real.pi * a * ∑ i, (p.2 i : ℂ) ^ 2)) := by
      refine h_prod_norm_summ.of_norm_bounded_eventually (g := fun p =>
          ‖Complex.exp (-Real.pi * a * (p.1 : ℂ) ^ 2)‖ *
          ‖Complex.exp (-Real.pi * a * ∑ i, (p.2 i : ℂ) ^ 2)‖) ?_
      refine Filter.Eventually.of_forall (fun p => ?_)
      rw [norm_mul]
    -- Compute:
    -- gaussianThetaMultiDim (d+1) a
    --   = ∑' n : Fin (d+1) → ℤ, cexp(-π·a·∑_i (n i)²)            (defn)
    --   = ∑' (z, n') : ℤ × (Fin d → ℤ), cexp(-π·a·∑_i (e (z,n') i)²)  (equiv)
    --   = ∑' (z, n'), cexp(-π·a·z²) · cexp(-π·a·∑_i (n' i)²)     (factorization)
    --   = (∑' z, cexp(-π·a·z²)) · (∑' n', cexp(-π·a·∑_i (n' i)²))  (tsum_mul_tsum)
    --   = theta1 a · gaussianThetaMultiDim d a                    (defn)
    --   = theta1 a · (theta1 a)^d                                 (IH)
    --   = (theta1 a)^(d+1)                                        (pow_succ)
    unfold gaussianThetaMultiDim
    rw [← e.tsum_eq]
    rw [show (∑' p : ℤ × (Fin d → ℤ),
            Complex.exp (-Real.pi * a * ∑ i, ((e p) i : ℂ) ^ 2)) =
        ∑' p : ℤ × (Fin d → ℤ),
          Complex.exp (-Real.pi * a * (p.1 : ℂ) ^ 2) *
          Complex.exp (-Real.pi * a * ∑ i, (p.2 i : ℂ) ^ 2) from
        tsum_congr (fun p => h_e_apply p.1 p.2)]
    rw [← h_1d.tsum_mul_tsum h_d_summ h_prod_summ]
    -- Apply IH and pow_succ.
    show theta1 a * (∑' n : Fin d → ℤ,
            Complex.exp (-Real.pi * a * ∑ i, (n i : ℂ) ^ 2)) =
        (theta1 a) ^ (d + 1)
    rw [show (∑' n : Fin d → ℤ,
              Complex.exp (-Real.pi * a * ∑ i, (n i : ℂ) ^ 2)) =
            gaussianThetaMultiDim d a from rfl]
    rw [IH ha, pow_succ]
    ring

/-- **d-D Jacobi theta modular transformation** (PROVED):
For `Re(a) > 0`,
  `gaussianThetaMultiDim d a = (1/a^(d/2)) · gaussianThetaMultiDim d (1/a)`.

That is, `∑' n : Fin d → ℤ, cexp(-π·a·∑_i (n i)²) = (1/a^(d/2)) · ∑' n, cexp(-π·(1/a)·∑_i (n i)²)`.

Derived by:
1. `gaussianThetaMultiDim d a = (theta1 a)^d` (factorization, by induction).
2. `theta1 a = 1/a^(1/2) · theta1 (1/a)` (Mathlib's 1-D theta).
3. Raise to the d-th power and reverse the factorization. -/
theorem gaussianThetaMultiDim_modular
    {d : ℕ} {a : ℂ} (ha : 0 < a.re) :
    gaussianThetaMultiDim d a =
      (1 / a ^ ((d : ℂ) / 2)) * gaussianThetaMultiDim d a⁻¹ := by
  have ha_ne : a ≠ 0 := fun h => by simp [h] at ha
  have h_inv_re : 0 < (a⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos ha (Complex.normSq_pos.mpr ha_ne)
  -- Step 1: reduce to (theta1 a)^d = (1/a^(d/2)) · (theta1 (1/a))^d via 1-D theta.
  rw [gaussianThetaMultiDim_eq_theta1_pow d ha]
  rw [gaussianThetaMultiDim_eq_theta1_pow d h_inv_re]
  -- Express theta1 (1/a) = theta1 a⁻¹ ⇒ matches what we need.
  -- The 1-D theta states theta1 a = 1/a^(1/2) · ∑' n, cexp(-π/a · n²).
  -- We need to identify ∑' n, cexp(-π/a · n²) = theta1 a⁻¹.
  have h_theta1_eq : theta1 a⁻¹ =
      ∑' n : ℤ, Complex.exp (-Real.pi / a * (n : ℂ) ^ 2) := by
    unfold theta1
    refine tsum_congr (fun n => ?_)
    rw [show (-Real.pi * a⁻¹ : ℂ) = -Real.pi / a from by rw [div_eq_mul_inv]]
  have h_1d_modular : theta1 a = 1 / a ^ (1 / 2 : ℂ) * theta1 a⁻¹ := by
    rw [h_theta1_eq]
    exact Complex.tsum_exp_neg_mul_int_sq ha
  -- Substitute and simplify.
  rw [h_1d_modular]
  -- Goal: (1/a^(1/2) · theta1 a⁻¹)^d = (1/a^(d/2)) · (theta1 a⁻¹)^d
  rw [mul_pow]
  congr 1
  -- (1/a^(1/2))^d = 1/a^(d/2)
  rw [div_pow, one_pow]
  -- Reduce to (a^(1/2))^d = a^(d/2).
  -- For arg condition on cpow_mul, note Re(a) > 0 implies |arg a| < π/2.
  have h_arg : |a.arg| < Real.pi / 2 :=
    (Complex.abs_arg_lt_pi_div_two_iff).mpr (Or.inl ha)
  have h_arg_neg_pi : -Real.pi < a.arg := by
    rw [abs_lt] at h_arg
    linarith [Real.pi_pos]
  have h_arg_pi : a.arg ≤ Real.pi := by
    rw [abs_lt] at h_arg
    linarith [Real.pi_pos]
  have h_log_im : (Complex.log a).im = a.arg := Complex.log_im a
  -- Compute (a^(1/2))^d = a^((1/2)·d) via cpow_mul.
  rw [show ((a ^ (1 / 2 : ℂ)) ^ d : ℂ) = (a ^ (1 / 2 : ℂ)) ^ ((d : ℕ) : ℂ) from
      (Complex.cpow_natCast (a ^ (1 / 2 : ℂ)) d).symm]
  rw [← Complex.cpow_mul]
  · congr 1
    push_cast
    ring
  · -- (Complex.log a * (1 / 2)).im > -π
    rw [Complex.mul_im, h_log_im]
    rw [show ((1 / 2 : ℂ).re : ℝ) = (1 / 2 : ℝ) from by simp,
        show ((1 / 2 : ℂ).im : ℝ) = 0 from by simp]
    rw [show ((Complex.log a).re : ℝ) = ((Complex.log a).re : ℝ) from rfl]
    have h1 : a.arg * (1 / 2 : ℝ) > -Real.pi := by
      rw [abs_lt] at h_arg
      nlinarith [Real.pi_pos]
    linarith [h1]
  · -- (Complex.log a * (1 / 2)).im ≤ π
    rw [Complex.mul_im, h_log_im]
    rw [show ((1 / 2 : ℂ).re : ℝ) = (1 / 2 : ℝ) from by simp,
        show ((1 / 2 : ℂ).im : ℝ) = 0 from by simp]
    have h2 : a.arg * (1 / 2 : ℝ) ≤ Real.pi := by
      rw [abs_lt] at h_arg
      nlinarith [Real.pi_pos]
    linarith [h2]
