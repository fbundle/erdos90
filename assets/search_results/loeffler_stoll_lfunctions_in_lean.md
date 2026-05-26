# Loeffler–Stoll 2025 — formalizing L-functions in Lean

**Paper:** D. Loeffler, M. Stoll, *"Formalizing zeta and L-functions in Lean"*,
*Annals of Formalized Mathematics* 1 (2025), 43–56.  arXiv:2503.00959.
**Local PDF:** `assets/loeffler_formalizing_lfunctions.pdf` (7 pages).

## Why this matters

This is the **definitive recent overview** of Mathlib's L-function
formalization.  Confirms the state of art and identifies gaps directly
relevant to our remaining sorries.

## What Mathlib has (confirmed by the paper)

### Zeta function
- `riemannZeta` — definition
- `riemannZeta_two` — Basel problem ζ(2) = π²/6
- `riemannZeta_euler_product` — Euler product
- **`riemannZeta_one_sub` — functional equation relating ζ(s) and ζ(1-s)**
- `riemannZeta_ne_zero_of_one_le_re` — nonvanishing on Re(s) ≥ 1
- `RiemannHypothesis` — formal statement (not proved)

### Dirichlet L-functions
- Analogous results, including non-vanishing on Re(s) ≥ 1
- Dirichlet's theorem on primes in AP (`Nat.setOf_prime_and_eq_mod_infinite`)

### Method used
- **Theta-function proof** of analytic continuation + functional equation.
  This is the approach we'd need to follow for Dedekind zeta.
- Uses Poisson summation formula and Gaussian integrals.

### Infrastructure pieces
- Approximately 1400 LOC for basic L-series theory in `Mathlib/NumberTheory/LSeries/`
- ~500 LOC for Euler product
- ~1400 LOC for Fourier analysis pieces:
  - Uniform convergence of Fourier series
  - Fourier transforms on ℝ
  - Poisson summation formula
- Jacobi theta function (1-var and 2-var) + transformation law `θ(-1/τ) = √(-iτ)·θ(τ)`
- Recent: `SchwartzMap.tsum_eq_tsum_fourierIntegral` — Poisson summation for
  Schwartz functions (1-D)

## Critical insight for our sorries

> To extend this to Dirichlet character L-series, it is necessary to consider
> the more general two-variable theta function (formalized as `jacobiTheta₂`).

Analogously, **for the Dedekind zeta of a number field K of degree n, we'd
need an n-variable theta function on `mixedSpace K`**.  This is the precise
gap.

## Confirmed Mathlib gap

Mathlib has Poisson summation only for `f : ℝ → ℂ` (1-D).  No multi-D version.
The Schwartz-Poisson summation (`SchwartzMap.tsum_eq_tsum_fourierIntegral`)
is also 1-D.

The path to multi-D:
1. Schwartz functions on `EuclideanSpace ℝ ι` (Mathlib has this).
2. Multi-D Fourier transform (Mathlib has this via
   `fourierIntegral` on finite-dim spaces).
3. Multi-D Poisson summation on ZLattices.  **Missing.**

## Active formalization projects mentioned

- **PrimeNumberTheorem+** by Alex Kontorovich + Terry Tao.
  Recently formalized PNT via Wiener–Ikehara (should be merged into Mathlib).
  Plans: explicit error term, primes in AP asymptotics.
- **Heather Macbeth** — substantial Fourier theory contributions
- **S. Gouëzel** — Schwartz function Fourier transform

## Implications for our sorries

For sorries 3 + 4 (`regulator_lower_bound_cm`, `dedekind_residue_upper_bound_cm`):
- The Loeffler–Stoll machinery for Riemann zeta is a PROVEN template.
  Generalizing to Dedekind zeta of a number field follows the SAME architecture
  but with multi-D theta functions and Poisson summation.
- Active areas of work (PNT+, Gouëzel's Schwartz work) provide complementary
  infrastructure.

For sorries 1 + 2 (class field theory + Chebotarev):
- The L-function half of Chebotarev can leverage `Dirichlet` infrastructure
  for ABELIAN extensions.  Generalizing to non-abelian K (needed for the BRD
  tower) requires Hecke characters — not covered by Loeffler–Stoll's paper
  but the L-function template would still apply.

## Bottom line

The Loeffler–Stoll paper is the **best modern reference** for understanding
Mathlib's L-function state and how to extend it.  Anyone closing our off-path
sorries should read this paper carefully and follow the same theta-function +
Poisson-summation architecture.
