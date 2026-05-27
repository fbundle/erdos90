/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Mathlib
import Erdos90.Mathlib4_Extra.Analysis.Fourier.GaussianThetaMultiDim

/-!
# Number-field theta function `θ_K` (Step C2)

For a number field `K`, define the L²-squared norm of the mixed embedding
explicitly (Mathlib's `mixedSpace K = Prod` doesn't carry a default L²
inner-product norm — only the L∞ Prod-sup norm) as
```
normSq_mixedEmbedding K a := ∑_{w real} (σ_w a)² + ∑_{w complex} |σ_w a|²
```
and the theta function
```
numberFieldTheta K t := ∑'_{a ∈ 𝓞_K} cexp(-π · t · normSq_mixedEmbedding K (a : K))
```

The modular transformation `θ_K(1/t) = √|d_K| · t^(n/2) · θ_K(t)` follows
from Poisson summation on the lattice `mixedEmbedding K (𝓞_K)`.  Decomposed
into named postulates below; the integer-lattice special case (which is
the analytic primitive) is PROVED as `gaussianThetaMultiDim_modular` in
`Mathlib4_Extra/Analysis/Fourier/GaussianThetaMultiDim.lean` (Step B).
-/

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace

variable (K : Type*) [Field K] [NumberField K]

/-- L²-squared norm of the mixed embedding of `a ∈ K`:
`∑_{w real} (σ_w a)² + ∑_{w complex} |σ_w a|²`. -/
noncomputable def normSq_mixedEmbedding (a : K) : ℝ := by
  classical
  exact (∑ w : {w : InfinitePlace K // IsReal w}, (mixedEmbedding K a).1 w ^ 2) +
    (∑ w : {w : InfinitePlace K // IsComplex w}, ‖(mixedEmbedding K a).2 w‖ ^ 2)

/-- The theta function of `K`:
`θ_K(t) := ∑'_{a ∈ 𝓞_K} cexp(-π · t · normSq_mixedEmbedding K (a : K))`. -/
noncomputable def numberFieldTheta (t : ℝ) : ℂ :=
  ∑' a : 𝓞 K,
    Complex.exp (-Real.pi * t * normSq_mixedEmbedding K (a : K))

/-! ### Convergence of `θ_K(t)` for `t > 0`

We prove `Summable (fun a : 𝓞 K => cexp(-π·t·normSq_mixedEmbedding K (a : K)))`
for `t > 0` via:
1. Reduce to summability over coordinate space `(idx → ℤ)` via the integral
   basis `RingOfIntegers.basis K`.
2. Express `normSq_mixedEmbedding K (∑_i k_i • α_i)` as a positive-definite
   quadratic form `Q : (idx → ℝ) → ℝ`.
3. Lower-bound `Q k ≥ λ · ‖k‖²` via extreme value theorem on the unit sphere
   (compact since idx is finite, Q continuous + positive on it).
4. Compare with the Gaussian sum on `(idx → ℤ)` proved as Step B
   (`summable_cexp_neg_pi_mul_finset_sum_sq` in `GaussianThetaMultiDim.lean`).
-/

/-- The integral basis of `𝓞 K` as a ℤ-module (Mathlib's `RingOfIntegers.basis K`). -/
local notation3 "ιK" => Module.Free.ChooseBasisIndex ℤ (𝓞 K)

/-- The basis vectors, viewed in `mixedSpace K` via `mixedEmbedding`. -/
noncomputable def basisInMixed (i : ιK) : mixedEmbedding.mixedSpace K :=
  mixedEmbedding K (((RingOfIntegers.basis K) i : 𝓞 K) : K)

/-- The "real expansion" of `normSq_mixedEmbedding` via the integral basis.
For `k : ιK → ℝ`, this is `‖∑_i k_i • basisInMixed K i‖²` in `mixedSpace K`'s
L²-norm convention (the explicit ∑_real + ∑_complex form). -/
noncomputable def basisQuadForm (k : ιK → ℝ) : ℝ := by
  classical
  let v : mixedEmbedding.mixedSpace K := ∑ i, k i • basisInMixed K i
  exact (∑ w : {w : InfinitePlace K // IsReal w}, v.1 w ^ 2) +
    (∑ w : {w : InfinitePlace K // IsComplex w}, ‖v.2 w‖ ^ 2)

/-- For integer coordinates `k : ιK → ℤ`, the basis expansion in `K`
recovers the corresponding ring-of-integers element via the basis. -/
theorem basisQuadForm_eq_normSq (k : ιK → ℤ) :
    basisQuadForm K (fun i => ((k i : ℤ) : ℝ)) =
      normSq_mixedEmbedding K
        ((((RingOfIntegers.basis K).equivFun.symm k : 𝓞 K)) : K) := by
  sorry

/-- The map from coordinates `(ιK → ℤ)` to ring-of-integers `𝓞 K`
via `Basis.equivFun.symm`. -/
noncomputable def basisCoordSymm (k : ιK → ℤ) : 𝓞 K :=
  (RingOfIntegers.basis K).equivFun.symm k

/-- The map `basisCoordSymm` is bijective (it's the inverse of a Basis equivalence). -/
theorem basisCoordSymm_bijective : Function.Bijective (basisCoordSymm K) :=
  (RingOfIntegers.basis K).equivFun.symm.bijective

/-- `Equiv` between `ιK → ℤ` and `𝓞 K`. -/
noncomputable def basisCoordEquiv : (ιK → ℤ) ≃ 𝓞 K :=
  (RingOfIntegers.basis K).equivFun.toEquiv.symm

/-! ### Positive-definiteness of `basisQuadForm` and lower bound

We prove `∃ λ > 0, ∀ k : ιK → ℝ, basisQuadForm K k ≥ λ · ‖k‖²` via:
- `basisQuadForm K` is continuous (polynomial in the coords).
- Positive at every nonzero `k` (since the basis is linearly independent
  in mixedSpace K, via injectivity of mixedEmbedding K).
- Extreme value theorem on the unit sphere of `(ιK → ℝ)` gives a positive
  minimum.
- Homogeneity (degree 2) gives the bound for all `k`.
-/

/-- `basisQuadForm K k` is continuous in `k`. -/
theorem basisQuadForm_continuous : Continuous (basisQuadForm K) := by
  classical
  unfold basisQuadForm
  -- The expression is polynomial in k (linear combos of finite sums).
  fun_prop

/-- `basisQuadForm K k ≥ 0` (it's a sum of squares). -/
theorem basisQuadForm_nonneg (k : ιK → ℝ) : 0 ≤ basisQuadForm K k := by
  classical
  unfold basisQuadForm
  positivity

/-- Positive-definiteness: `basisQuadForm K k = 0 ↔ k = 0`.

Direction `←` is trivial. Direction `→` uses linear independence of
`basisInMixed K i` over ℝ (since `mixedEmbedding K` is injective on `K`
and the basis is linearly independent over ℚ, hence over ℝ after extension). -/
theorem basisQuadForm_eq_zero_iff (k : ιK → ℝ) :
    basisQuadForm K k = 0 ↔ k = 0 := by
  classical
  sorry

/-- Lower bound: there exists `λ > 0` such that `basisQuadForm K k ≥ λ · ‖k‖²`
for all `k : ιK → ℝ`.  Proof via extreme value theorem on the unit sphere. -/
theorem basisQuadForm_lower_bound :
    ∃ lam : ℝ, 0 < lam ∧ ∀ k : ιK → ℝ,
      lam * (∑ i, (k i) ^ 2) ≤ basisQuadForm K k := by
  classical
  sorry

/-! ### Lifted Step B + final assembly

The infrastructure above (basisInMixed, basisQuadForm) and the lower-bound
`basisQuadForm_lower_bound` (sorried — extreme value theorem application)
together with Step B's `summable_cexp_neg_pi_mul_finset_sum_sq` give the
summability via:
- bound `‖cexp(-π·t·normSq)‖ ≤ exp(-π·t·λ·∑(k i)²)`
- transfer summability from `Fin (card ιK) → ℤ` (Step B) to `ιK → ℤ` via
  the Fintype.equivFin bijection
- transfer summability from `ιK → ℤ` to `𝓞 K` via the integral basis
  equivalence.

The proof is sketched but final assembly is left sorried since closing it
requires multiple ~50-LOC sub-steps (Equiv.piCongrLeft transfer chain,
real-vs-complex Re manipulation, basis-coord identification).  These are
mechanical Lean engineering, not new mathematics — they're the kind of
"plumbing" that Mathlib could absorb in a focused PR.
-/

/-- **C2.summ — Convergence of `θ_K(t)` for `t > 0`** — sorried.

PROOF STRUCTURE (modulo `basisQuadForm_lower_bound`):
1. Get `λ > 0` with `basisQuadForm K k ≥ λ · ‖k‖²` (positive-definiteness).
2. Equivalence `𝓞 K ≃ (ιK → ℤ)` via the basis sends our function to
   `fun k => cexp(-π·t·basisQuadForm(k : ιK → ℝ))`.
3. Norm bound via `λ`: `‖cexp(-π·t·basisQuadForm(k))‖ = exp(-π·t·basisQuadForm(k)) ≤
   exp(-π·t·λ·∑(k i)²)`.
4. Step B lifted to fintype `ιK` (via `Fintype.equivFin`) gives summability
   of the bound.
5. `Summable.of_norm_bounded` finishes.

See preceding `basisQuadForm_lower_bound` for the positive-definiteness
lower-bound dependency. -/
theorem numberFieldTheta_summable_postulate
    (t : ℝ) (_ht : 0 < t) :
    Summable (fun a : 𝓞 K =>
      Complex.exp (-Real.pi * t * normSq_mixedEmbedding K (a : K))) :=
  sorry

/-- **C2.modular — Modular transformation of `θ_K`** (postulate).

For `t > 0`:
```
θ_K(1/t) = √|disc K| · t^(n/2) · θ_K(t)
```
where `n = [K:ℚ]`.

This follows from Poisson summation applied to the Gaussian on the lattice
`mixedEmbedding K (𝓞_K)` in `mixedSpace K`.

DECOMPOSITION:
1. **Lattice Poisson summation** — general lattice version of multi-D
   Poisson.  Integer-lattice special case PROVED as
   `gaussianThetaMultiDim_modular` (Step B).
2. **Gaussian Fourier transform** on the inner-product space `euclidean.mixedSpace K`
   — Mathlib's `fourier_gaussian_innerProductSpace` (PROVED, citation).
3. **Identify covol(𝓞_K) = √|disc K|** — Mathlib's
   `volume_fundamentalDomain_latticeBasis` (PROVED, modulo `(1/2)^{r₂}`
   normalisation factor). -/
def numberFieldTheta_modular_postulate
    (t : ℝ) (_ht : 0 < t) :
    numberFieldTheta K (1 / t) =
      ((Real.sqrt |(NumberField.discr K : ℝ)| : ℝ) : ℂ) *
        ((t ^ ((Module.finrank ℚ K : ℝ) / 2) : ℝ) : ℂ) *
        numberFieldTheta K t :=
  sorry

/-! ## Sub-postulates for `numberFieldTheta_modular_postulate` -/

section ModularSubPostulates

open MeasureTheory ZSpan
open scoped FourierTransform RealInnerProductSpace Classical

/-! ### Decomposition of `lattice_poisson_postulate`

The full statement (for any Schwartz `f` on any inner product space and
any full-rank lattice) reduces via change-of-basis to "Gaussian Poisson
for a positive-definite quadratic form on `ℤ^d`":
```
∑'_{n ∈ ℤ^d} cexp(-π · a · nᵀ Q n) = (det Q)^(-1/2) · a^(-d/2) ·
  ∑'_{n ∈ ℤ^d} cexp(-π · a⁻¹ · nᵀ Q⁻¹ n)
```
for `Re(a) > 0` and symmetric positive-definite `Q`.

Special cases (with progressively more general `Q`):

* **Identity case** `Q = I`: PROVED as `gaussianThetaMultiDim_modular`
  (Step B).
* **Diagonal case** `Q = diag(λ_i)`: PROVED as `thetaAniso_modular`
  (C1).  Covers any lattice that becomes axis-aligned after an
  orthogonal change of basis.
* **General PSD case**: still open in Mathlib v4.30; would follow from
  full multi-D Schwartz Poisson summation + linear change of variables.

For the number-field application, the CM lattice's Gram matrix is the
**trace form** on `𝓞_K`, which is generally not diagonal in any obvious
integral basis.  Reducing it to the diagonal case requires a basis
adapted to the spectral decomposition of the trace form — which may not
be an integral basis.
-/

/-- **C2.modular.poisson.diagonal — Diagonal Gaussian-Poisson** (PROVED).

For per-coordinate complex scales `a : Fin d → ℂ` with `Re(a i) > 0`,
the diagonal Jacobi theta has the modular transformation
```
∑'_{n} cexp(-π·∑_i (a i)·(n i)²) =
  (∏_i (a i)^(-1/2)) · ∑'_{n} cexp(-π·∑_i (a i)⁻¹·(n i)²).
```

This is `thetaAniso_modular` re-exported.  It covers the case where the
lattice's Gram matrix is diagonal in an integral basis. -/
theorem lattice_poisson_diagonal_postulate
    {d : ℕ} (a : Fin d → ℂ) (ha : ∀ i, 0 < (a i).re) :
    (∑' n : Fin d → ℤ,
        Complex.exp (-Real.pi * ∑ i, (a i) * (n i : ℂ) ^ 2)) =
      (∏ i, 1 / (a i) ^ (1 / 2 : ℂ)) *
        ∑' n : Fin d → ℤ,
          Complex.exp (-Real.pi * ∑ i, (a i)⁻¹ * (n i : ℂ) ^ 2) :=
  SchwartzMap.thetaAniso_modular a ha

/-- The Gaussian sum on `ℤ^d` for a quadratic form `Q`. -/
noncomputable def gaussianThetaForm (d : ℕ)
    (Q : Matrix (Fin d) (Fin d) ℝ) (a : ℂ) : ℂ :=
  ∑' n : Fin d → ℤ, Complex.exp (-Real.pi * a *
    ∑ i, ∑ j, (Q i j : ℂ) * (n i : ℂ) * (n j : ℂ))

/-- **C2.modular.poisson.general — General Gaussian-Poisson** (statement).

For symmetric positive-definite `Q : Matrix (Fin d) (Fin d) ℝ`,
  `gaussianThetaForm d Q a = (det Q)^(-1/2) · a^(-d/2) · gaussianThetaForm d Q⁻¹ a⁻¹`
for `Re(a) > 0`. -/
def lattice_poisson_general_postulate
    {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (_hQ_sym : Q.IsSymm)
    (_hQ_pd : True /- Q is positive definite -/)
    {a : ℂ} (_ha : 0 < a.re) : Prop :=
  gaussianThetaForm d Q a =
    ((Q.det : ℂ)) ^ (-(1 : ℂ) / 2) * a ^ (-(d : ℂ) / 2) *
      gaussianThetaForm d Q⁻¹ a⁻¹

/-! ### Special cases of `lattice_poisson_general_postulate` (PROVED) -/

/-- **d = 0** base case (PROVED): both sides equal 1 (empty product). -/
theorem lattice_poisson_general_zero_dim
    (Q : Matrix (Fin 0) (Fin 0) ℝ) (hQ_sym : Q.IsSymm)
    {a : ℂ} (ha : 0 < a.re) :
    lattice_poisson_general_postulate Q hQ_sym trivial ha := by
  unfold lattice_poisson_general_postulate gaussianThetaForm
  -- Both ∑' n : Fin 0 → ℤ sums reduce to 1 (singleton index set, exponent 0).
  have h_lhs : (∑' n : Fin 0 → ℤ, Complex.exp (-Real.pi * a *
        ∑ i : Fin 0, ∑ j : Fin 0, (Q i j : ℂ) * (n i : ℂ) * (n j : ℂ))) = 1 := by
    have h_one : ∀ n : Fin 0 → ℤ,
        Complex.exp (-Real.pi * a *
            ∑ i : Fin 0, ∑ j : Fin 0, (Q i j : ℂ) * (n i : ℂ) * (n j : ℂ)) = 1 := by
      intro n; simp
    rw [tsum_congr h_one, tsum_const]; simp
  have h_rhs : (∑' n : Fin 0 → ℤ, Complex.exp (-Real.pi * a⁻¹ *
        ∑ i : Fin 0, ∑ j : Fin 0, ((Q⁻¹ i j : ℝ) : ℂ) * (n i : ℂ) * (n j : ℂ))) = 1 := by
    have h_one : ∀ n : Fin 0 → ℤ,
        Complex.exp (-Real.pi * a⁻¹ *
            ∑ i : Fin 0, ∑ j : Fin 0, ((Q⁻¹ i j : ℝ) : ℂ) * (n i : ℂ) * (n j : ℂ)) = 1 := by
      intro n; simp
    rw [tsum_congr h_one, tsum_const]; simp
  rw [h_lhs, h_rhs]
  -- `det Q = 1` for Q : Matrix (Fin 0) (Fin 0) (empty matrix).
  have h_det : Q.det = 1 := Matrix.det_isEmpty
  rw [h_det]
  show (1 : ℂ) = (1 : ℂ) ^ (-(1 : ℂ) / 2) * a ^ (-((0 : ℕ) : ℂ) / 2) * 1
  rw [Complex.one_cpow]
  rw [show -((0 : ℕ) : ℂ) / 2 = 0 from by push_cast; ring]
  rw [Complex.cpow_zero]
  ring

/-- Helper: for `q : ℝ` positive and `a : ℂ` nonzero, `((q : ℂ) * a)^c = q^c * a^c`. -/
theorem ofReal_pos_mul_cpow_eq {q : ℝ} (hq : 0 < q) {a : ℂ} (ha : a ≠ 0) (c : ℂ) :
    ((q : ℂ) * a) ^ c = ((q : ℂ)) ^ c * a ^ c := by
  have h_q_ne : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hq)
  have h_prod_ne : (q : ℂ) * a ≠ 0 := mul_ne_zero h_q_ne ha
  rw [Complex.cpow_def_of_ne_zero h_prod_ne,
      Complex.cpow_def_of_ne_zero h_q_ne,
      Complex.cpow_def_of_ne_zero ha]
  rw [Complex.log_ofReal_mul hq ha]
  rw [add_mul]
  rw [Complex.exp_add]
  congr 2
  -- The (log q : ℂ) needs to match the ofReal log.
  simp [Complex.ofReal_log hq.le]

/-- **d = 1** case (PROVED): reduces to Mathlib's `Complex.tsum_exp_neg_mul_int_sq`.

For `Q : Matrix (Fin 1) (Fin 1) ℝ` with `Q 0 0 > 0`, the Gram-matrix
Gaussian sum reduces to the 1-D Jacobi theta at parameter `b := a · Q 0 0`. -/
theorem lattice_poisson_general_one_dim_postulate
    (Q : Matrix (Fin 1) (Fin 1) ℝ) (hQ_sym : Q.IsSymm)
    (hQ_pos : 0 < Q 0 0) {a : ℂ} (ha : 0 < a.re) :
    lattice_poisson_general_postulate Q hQ_sym trivial ha := by
  unfold lattice_poisson_general_postulate gaussianThetaForm
  set q : ℝ := Q 0 0 with hq_def
  have h_q_pos : 0 < q := hQ_pos
  have h_q_ne_ℝ : (q : ℝ) ≠ 0 := ne_of_gt h_q_pos
  have h_q_ne : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h_q_ne_ℝ
  have h_a_ne : a ≠ 0 := by
    intro h_eq; rw [h_eq] at ha; simp at ha
  -- Equivalence (Fin 1 → ℤ) ≃ ℤ.
  let e : ℤ ≃ (Fin 1 → ℤ) := (Equiv.funUnique (Fin 1) ℤ).symm
  -- Reduce LHS sum to 1-D Gaussian sum with parameter a·q.
  have h_lhs_step : (∑' n : Fin 1 → ℤ, Complex.exp (-Real.pi * a *
        ∑ i : Fin 1, ∑ j : Fin 1, (Q i j : ℂ) * (n i : ℂ) * (n j : ℂ))) =
      ∑' k : ℤ, Complex.exp (-Real.pi * (a * (q : ℂ)) * (k : ℂ) ^ 2) := by
    rw [← e.tsum_eq]
    refine tsum_congr (fun k => ?_)
    have h_n_0 : ((e k : Fin 1 → ℤ) 0 : ℂ) = (k : ℂ) := by
      simp [e, Equiv.funUnique]
    simp only [Fin.sum_univ_one, h_n_0]
    congr 1
    rw [← hq_def]
    ring
  -- Inverse of the 1x1 matrix: Q⁻¹ 0 0 = 1/q.
  have h_q_inv_val : (Q⁻¹) 0 0 = 1 / q := by
    rw [Matrix.inv_def, Matrix.adjugate_fin_one, Matrix.det_fin_one]
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, Ring.inverse_eq_inv',
               smul_eq_mul, mul_one, ← hq_def]
    rw [inv_eq_one_div]
  -- Reduce RHS sum.
  have h_rhs_step : (∑' n : Fin 1 → ℤ, Complex.exp (-Real.pi * a⁻¹ *
        ∑ i : Fin 1, ∑ j : Fin 1, ((Q⁻¹ i j : ℝ) : ℂ) * (n i : ℂ) * (n j : ℂ))) =
      ∑' k : ℤ, Complex.exp (-Real.pi * (a * (q : ℂ))⁻¹ * (k : ℂ) ^ 2) := by
    rw [← e.tsum_eq]
    refine tsum_congr (fun k => ?_)
    have h_n_0 : ((e k : Fin 1 → ℤ) 0 : ℂ) = (k : ℂ) := by
      simp [e, Equiv.funUnique]
    simp only [Fin.sum_univ_one, h_n_0]
    rw [h_q_inv_val]
    congr 1
    push_cast
    field_simp
  rw [h_lhs_step, h_rhs_step]
  -- Apply Mathlib's 1-D theta with b = a·q.
  have ha_q_re : 0 < (a * (q : ℂ)).re := by
    rw [Complex.mul_re]
    have h_re : ((q : ℂ)).re = q := by simp
    have h_im : ((q : ℂ)).im = 0 := by simp
    rw [h_re, h_im]
    nlinarith [ha, h_q_pos]
  have h_1d := Complex.tsum_exp_neg_mul_int_sq ha_q_re
  rw [h_1d]
  -- det Q = q.
  have h_det : Q.det = q := by rw [Matrix.det_fin_one, ← hq_def]
  rw [h_det]
  -- Goal: 1/(a·q)^(1/2) · ∑ cexp(-π/(a·q)·k²)
  --     = q^(-1/2) · a^(-1/2) · ∑ cexp(-π·(a·q)⁻¹·k²)
  -- Replace -Real.pi / (a·q) with -Real.pi · (a·q)⁻¹.
  have h_sum_eq : (∑' k : ℤ, Complex.exp (-Real.pi / (a * (q : ℂ)) * (k : ℂ) ^ 2)) =
      ∑' k : ℤ, Complex.exp (-Real.pi * (a * (q : ℂ))⁻¹ * (k : ℂ) ^ 2) := by
    refine tsum_congr (fun k => ?_)
    rw [show -((Real.pi : ℂ)) / (a * (q : ℂ)) = -Real.pi * (a * (q : ℂ))⁻¹ from
        by rw [div_eq_mul_inv]]
  rw [h_sum_eq]
  -- Match the coefficient: 1/(a·q)^(1/2) = q^(-1/2) · a^(-1/2).
  -- Strategy: reduce both to a common form via ofReal_pos_mul_cpow_eq.
  have h_mul_cpow : (a * (q : ℂ)) ^ ((1 : ℂ) / 2) =
      a ^ ((1 : ℂ) / 2) * ((q : ℂ)) ^ ((1 : ℂ) / 2) := by
    rw [mul_comm a]
    rw [ofReal_pos_mul_cpow_eq h_q_pos h_a_ne]
    ring
  -- Goal: 1 / (a * ↑q) ^ (1/2) * (∑' ...) = ↑q ^ (-1 / 2) * a ^ (-↑1 / 2) * (∑' ...)
  -- The mixed `(-1/2)` vs `(-↑1/2)` is harmless via push_cast.
  -- Prove the coefficient equality directly.
  have h_coef : (1 : ℂ) / (a * (q : ℂ)) ^ ((1 : ℂ) / 2) =
      ((q : ℂ)) ^ (-(1 : ℂ) / 2) * a ^ (-((1 : ℕ) : ℂ) / 2) := by
    rw [show -((1 : ℕ) : ℂ) / 2 = -((1 : ℂ) / 2) from by push_cast; ring]
    rw [show -(1 : ℂ) / 2 = -((1 : ℂ) / 2) from by ring]
    rw [Complex.cpow_neg ((q : ℂ)), Complex.cpow_neg a]
    rw [h_mul_cpow]
    have h_q_pow_ne : ((q : ℂ)) ^ ((1 : ℂ) / 2) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt h_q_pos)))
    have h_a_pow_ne : a ^ ((1 : ℂ) / 2) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl h_a_ne)
    field_simp
  rw [h_coef]

/-- **C2.modular.poisson — Lattice Poisson summation** (postulate, retained
as a high-level header pointing to the decomposed sub-postulates).

For a full-rank ℤ-lattice `L` in a finite-dim ℝ-inner-product space `V`,
and Schwartz `f : V → ℂ`,
```
∑'_{x ∈ L} f(x) = (covol L)⁻¹ · ∑'_{ξ ∈ L*} 𝓕(f)(ξ)
```
where `L* := {ξ : V | ∀ x ∈ L, ⟨x, ξ⟩ ∈ ℤ}` is the dual lattice and
`covol L := volume (fundamentalDomain (latticeBasis L))`.

DECOMPOSITION:
* For Gaussians (the only case used here): the lattice Poisson reduces
  to `lattice_poisson_general_postulate` after picking an integral basis
  for `L` and computing the Gram matrix `Q := Bᵀ B` (B = basis matrix).
* The integer-lattice and diagonal-Gram special cases are PROVED via
  `gaussianThetaMultiDim_modular` and `lattice_poisson_diagonal_postulate`
  above.
* The fully general Schwartz `f` (not just Gaussian) would additionally
  require multi-D Schwartz Poisson (`tsum_eq_tsum_fourier_multi_postulate`
  in `PoissonProd.lean`).  Not used here. -/
def lattice_poisson_postulate : True := sorry

/-- **C2.modular.gaussian — d-D Gaussian Fourier transform** (PROVED).

Direct restatement of Mathlib's `fourier_gaussian_innerProductSpace`. -/
theorem gaussian_fourier_innerProduct_postulate
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {b : ℂ} (hb : 0 < b.re) (w : V) :
    𝓕 (fun (v : V) ↦ Complex.exp (-b * ‖v‖ ^ 2)) w =
      (Real.pi / b) ^ (Module.finrank ℝ V / 2 : ℂ) *
        Complex.exp (-Real.pi ^ 2 * ‖w‖ ^ 2 / b) :=
  fourier_gaussian_innerProductSpace hb w

/-- **C2.modular.covolume — `vol(fundDomain) = √|disc K|` up to the
2^(r₂) factor** (PROVED).

Direct restatement of Mathlib's `volume_fundamentalDomain_latticeBasis`. -/
theorem covolume_eq_sqrt_disc_postulate
    (K : Type*) [Field K] [NumberField K] :
    volume (fundamentalDomain (latticeBasis K)) =
      (2 : ENNReal)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K *
        NNReal.sqrt ‖NumberField.discr K‖₊ :=
  NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis K

end ModularSubPostulates
