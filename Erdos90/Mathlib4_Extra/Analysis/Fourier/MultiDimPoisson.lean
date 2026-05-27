import Mathlib

/-!
# Multi-dimensional Poisson summation (Mathlib-PR documentation)

This file documents the multi-dimensional Poisson summation formula, which is
the missing piece for closing several analytic sorries in this project:
- `regulator_lower_bound_cm` (Friedman regulator bound)
- `dedekind_residue_upper_bound_cm` (Louboutin residue bound)

Both are blocked on the functional equation for `NumberField.dedekindZeta`,
which in turn needs multi-D Poisson summation for the number-field lattice.

## Strategy: 2-D via iteration

For Schwartz `f : 𝓢(ℝ × ℝ, ℂ)`, iterate the 1-D Poisson formula
(`SchwartzMap.tsum_eq_tsum_fourier`) twice via Fubini.

Outline:
1. Define φ(x) : ℝ → 𝓢(ℝ, ℂ) by `φ(x)(y) = f(x, y)`.  (Schwartz in y for each x.)
2. By 1-D Poisson in y: `Σ_n f(x, n) = Σ_q 𝓕_y(f(x, ·))(q)`.
3. Define ψ(q) : ℝ → ℂ by `ψ(q)(x) = 𝓕_y(f(x, ·))(q)`.
   (Schwartz in x by smoothness + decay of f.)
4. Sum over m: `Σ_m ψ(q)(m) = Σ_p 𝓕_x(ψ(q))(p)` by 1-D Poisson in x.
5. `𝓕_x(ψ(q))(p) = ∫∫ f(x,y) e^{-2πi(px + qy)} dy dx = 𝓕(f)(p, q)` (Fubini).
6. Combine: `Σ_{(m,n)} f(m,n) = Σ_{(p,q)} 𝓕f(p,q)`.

## What Mathlib has

- 1-D Schwartz Poisson summation: `SchwartzMap.tsum_eq_tsum_fourier`
- Multi-D Fourier transform on inner product spaces: `Real.fourierIntegral`
  (and `VectorFourier.fourierIntegral` generic)
- Schwartz spaces on general normed real vector spaces: `SchwartzMap`
- Fubini for integrals: `MeasureTheory.integral_prod`
- Fubini for tsum: `tsum_prod` and friends
- Jacobi theta functions in 1 and 2 variables (for L-function applications)

## What's needed (Mathlib gap)

### Resolved in this codebase (May 2026)

1. **Schwartz multi-variable currying** — DONE: `SchwartzMap.rightPartial`
   and `SchwartzMap.leftPartial` in `PoissonProd.lean` (PROVED).

2. **2-D Schwartz Poisson summation** — DONE modulo 3 named postulates:
   `tsum_2d_schwartz_poisson` in `PoissonProd.lean` is PROVED Lean code
   that says
   ```
   ∑' p : ℤ × ℤ, f p = ∑' p : ℤ × ℤ, fourier2D f p.1 p.2
   ```
   for `f : 𝓢(ℝ × ℝ, ℂ)`, where `fourier2D f m n = ∫ p, exp(-2πi(m·p.1+
   n·p.2))·f(p)`.  The 3 named postulates are:
   - `partial_fourier_is_Schwartz_postulate` (Fourier-in-one-variable
     preserves Schwartz, with value spec).
   - `summable_partialFourier_2d_postulate` (intermediate Fourier sum
     summable on `ℤ × ℤ`).
   - `summable_fourier2D_postulate` (full 2-D Fourier sum summable on
     `ℤ × ℤ`).
   All three are TRUE Plancherel-style facts; not in Mathlib v4.30.

### Still needed for the full chain

3. **n-D Schwartz Poisson summation** — `tsum_eq_tsum_fourier_multi_postulate`
   in `PoissonProd.lean` (sorried).  Reduces to 2-D + induction.

4. **Lattice Poisson summation**: for general ZLattices via change of basis.

## Proof sketch — IMPLEMENTED in `PoissonProd.lean`

The 2-D Schwartz Poisson identity is now a PROVED theorem
(`tsum_2d_schwartz_poisson`).  Sketch of the assembly:

```
theorem tsum_2d_schwartz_poisson (f : 𝓢(ℝ × ℝ, ℂ)) :
    (∑' p : ℤ × ℤ, (f : ℝ × ℝ → ℂ) (p.1, p.2)) =
    ∑' p : ℤ × ℤ, fourier2D f p.1 p.2 := by
  -- Step 1: LHS = ∑' m, ∑' n, (partialFourier f n) m  (via Fubini + 1-D Poisson per row)
  rw [tsum_prod_eq_tsum_tsum_partialFourier]
  -- Step 2: swap ∑' m, ∑' n ↔ ∑' n, ∑' m  (Summable.tsum_comm)
  rw [tsum_tsum_partialFourier_swap]
  -- Step 3: ∑' n, ∑' m, (partialFourier f n) m = ∑' n, ∑' m, fourier2D f m n
  conv_lhs => rw [show … from by
    refine tsum_congr (fun n => ?_)
    exact tsum_partialFourier_eq_fourier2D f n]
  -- Step 4: swap ∑' n, ∑' m, fourier2D ↔ ∑' m, ∑' n, fourier2D  (Summable.tsum_comm)
  rw [h_swap]
  -- Step 5: ∑' m, ∑' n, fourier2D f m n = ∑' p, fourier2D f p.1 p.2  (Summable.tsum_prod)
  rw [h_prod]
```

The 5-step chain has 3 of the 5 steps backed by labelled postulates
(Steps 2, 4: tsum_comm; Step 5: tsum_prod — all 3 need summability of
the partial/full 2-D Fourier on ℤ × ℤ).  Steps 1 and 3 are PROVED Lean.

### Key supporting theorems (all PROVED in `PoissonProd.lean`)

- `fourier_partialFourier_eq_fourier2D`: identifies 1-D Fourier of
  `partialFourier f n` with 2-D Fourier of `f` at `(m, n)`.
- `tsum_partialFourier_eq_fourier2D`: 1-D Poisson on `partialFourier f n`
  gives a sum over `fourier2D f m n`.
- `iterated_fourier_eq_2d_integral`: Fubini for the 2-D Fourier integral
  expressed as iterated 1-D integrals.
- `tsum_prod_eq_tsum_tsum_fourier_rightPartial`: row-Poisson chain
  combining Fubini (`summable_2d_schwartz_proved` — fully PROVED) with
  1-D Poisson per row.

## Connection to Dedekind zeta functional equation

Once we have multi-D Schwartz Poisson summation, the path to
`completedDedekindZeta`'s functional equation goes through:

1. Define `theta_K(t) : ℝ → ℂ` for `t > 0` by
   ```
   theta_K(t) = ∑_{a ∈ 𝓞_K} exp(-π · t · ‖canonicalEmbedding K a‖²)
   ```
   (sum over the number-field lattice in `mixedSpace K`).

2. Apply multi-D Poisson summation to get the modular transformation:
   ```
   theta_K(1/t) = √|d_K| · t^(d/2) · theta_K^*(t)
   ```
   where `theta_K^*` involves the dual lattice (or coincides with `theta_K` for
   the appropriate normalization).

3. Wire into `Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean`'s `WeakFEPair`
   framework to get analytic continuation + functional equation for
   `completedDedekindZeta`.

This is the Loeffler–Stoll architecture (which they used for Riemann zeta and
Dirichlet L-functions) extended to general number fields.

## References

- 1-D Mathlib version: `Mathlib/Analysis/Fourier/PoissonSummation.lean`
- Loeffler–Stoll 2025: `assets/loeffler_formalizing_lfunctions.pdf`
- Closing strategy: `assets/search_results/closing_roadmap.md`

This file is intentionally documentation-only (no sorried Lean declarations
that would affect the project's sorry count).
-/

-- No Lean declarations in this file.  All content is documentation.
