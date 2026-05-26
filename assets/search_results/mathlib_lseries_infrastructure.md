# Mathlib L-series infrastructure — what exists, what's missing

Survey conducted 2026-05-27 for closing `regulator_lower_bound_cm` and
`dedekind_residue_upper_bound_cm` (D3.2c + D3.2b).

## What Mathlib v4.30 HAS

### Core L-series framework
- `Mathlib/NumberTheory/LSeries/Basic.lean` — `LSeries` definition, convergence
- `Mathlib/NumberTheory/LSeries/Linearity.lean` — linearity properties
- `Mathlib/NumberTheory/LSeries/Convergence.lean` — convergence half-planes
- `Mathlib/NumberTheory/LSeries/Convolution.lean` — Dirichlet convolution
- `Mathlib/NumberTheory/LSeries/Deriv.lean` — derivatives
- `Mathlib/NumberTheory/LSeries/SumCoeff.lean` — Abel/Tauberian helpers

### Riemann zeta
- `Mathlib/NumberTheory/LSeries/RiemannZeta.lean`
- `riemannZeta`, `completedRiemannZeta`
- Analytic continuation past `s = 1`
- Functional equation `Λ(1 - s) = Λ(s)`
- Special values: `riemannZeta_neg_two_mul_nat_add_one`, etc.

### Dirichlet L-functions (extensive)
- `Mathlib/NumberTheory/LSeries/Dirichlet.lean` — basic
- `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean` — analytic
  continuation; defines `DirichletCharacter.LFunction`, `completedLFunction`,
  `gammaFactor`, `rootNumber`
- Functional equation:
  `completedLFunction χ (1 - s) = N ^ (s - 1/2) · rootNumber χ · completedLFunction χ⁻¹ s`
- `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` — non-vanishing on Re s = 1
- `Mathlib/NumberTheory/LSeries/Positivity.lean` — positivity in real ranges
- `Mathlib/NumberTheory/LSeries/PrimesInAP.lean` — Dirichlet's theorem on primes
  in AP (using L-function nonvanishing)
- `Mathlib/NumberTheory/LSeries/ZMod.lean` — L-functions over ZMod N
- `Mathlib/NumberTheory/LSeries/ZetaZeros.lean` — Riemann zeta zero locations

### Hurwitz zeta
- `Mathlib/NumberTheory/LSeries/HurwitzZeta.lean` — Hurwitz zeta function
- `HurwitzZetaEven`, `HurwitzZetaOdd`, `HurwitzZetaValues` — parity, special values

### Abstract framework for functional equations
- `Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean` — **the key infrastructure
  piece**.  Provides `WeakFEPair` and `StrongFEPair`:
  - Pair of functions `(f, g)` on positive reals with FE
    `f(1/x) = ε · x^k · g(x)`.
  - Their Mellin transforms have meromorphic continuation + FE
    `Λ(k - s) = ε · Λ'(s)`.
  - Used to build the FE for Riemann zeta and Dirichlet L-functions.

### Dedekind zeta
- `Mathlib/NumberTheory/NumberField/DedekindZeta.lean` (88 lines, SLIM)
  - Definition: `dedekindZeta K s := LSeries (n ↦ Nat.card {I // absNorm I = n}) s`
  - `dedekindZeta_residue K`: value of residue at s = 1
  - `tendsto_sub_one_mul_dedekindZeta_nhdsGT`: Dirichlet class number formula
    in limit form
  - **That's it.** No functional equation, no continuation past s = 1, no
    special values.

### Mellin transforms
- `Mathlib/Analysis/MellinTransform.lean`
- `mellin`, `mellinInv`, `mellinConvergent`
- Used by AbstractFuncEq

### Number field arithmetic (relevant)
- `Mathlib/NumberTheory/NumberField/Ideal/Asymptotics.lean` — ideal counting
  asymptotics (gives the residue at s=1 via Tauberian)

## What's MISSING (the gaps for our sorries)

### Functional equation for `dedekindZeta`
**Required for**: `regulator_lower_bound_cm`, `dedekind_residue_upper_bound_cm`.

Mathematically: define the "completed" Dedekind zeta
```
Λ_K(s) := |d_K|^(s/2) · Γ_ℝ(s)^{r₁} · Γ_ℂ(s)^{r₂} · ζ_K(s)
```
where `Γ_ℝ(s) := π^(-s/2) · Γ(s/2)` and `Γ_ℂ(s) := 2·(2π)^(-s) · Γ(s)`.

Then `Λ_K(1 - s) = Λ_K(s)`.

**Path forward via `AbstractFuncEq.lean`**:
1. Define the theta function `θ_K(t) := Σ_{a ∈ 𝓞_K} exp(-π · t · |a|²)` (suitable
   sum over the ring of integers via Minkowski embedding).
2. Show theta function inverts via Poisson summation:
   `θ_K(1/t) = √|d_K| · t^(d/2) · θ_K(t)` (roughly).
3. Wire into `AbstractFuncEq.WeakFEPair` or `StrongFEPair`.
4. Conclude analytic continuation + FE for `Λ_K`.

**Estimated lines of Lean**: substantial — probably 1000–2000 lines.
- Theta function definition + Poisson summation on `mixedSpace K` — needs
  Fourier analysis on `mixedSpace K` (Mathlib has some).
- Mellin transform identification — once theta is built, this is mostly
  technical.

### Hecke L-functions (for non-abelian K)
**Required for**: closure of CM-specific bounds for K not abelian over ℚ.

The BRD tower's CM fields are NOT abelian extensions of ℚ.  So we can't
just factor `ζ_K` as a product of Dirichlet L's.  Need general Hecke characters.

**Estimated lines of Lean**: VERY substantial — probably 3000–5000 lines just
for Hecke L-functions; longer for their functional equations.

### Explicit residue evaluation at `s = 0`
**Required for**: `regulator_lower_bound_cm` via Stark/Tate.

Once we have `dedekindZeta` continued and the functional equation, we can
evaluate at `s = 0`:
```
ζ_K(0) = -h_K · R_K / w_K · (something explicit involving signature)
```

Then `|ζ_K(0)| = h_K · R_K / w_K` gives `R_K = w_K · |ζ_K(0)| / h_K`.

Lower-bounding `ζ_K(0)` (Friedman's approach) then gives `R_K ≥ ...`.

**Friedman's specific bound**: requires positivity of certain integrals
involving theta functions.  Once the FE is in place, this is a moderate
analytic argument — probably 500–1000 lines.

## Recommended Mathlib PR priorities

Ordered by leverage (how many of our sorries each unblocks):

### PR 1: Dedekind zeta functional equation (UNLOCKS 2 sorries)
- Foundation: theta function + Poisson summation on `mixedSpace K`
- Wire into `AbstractFuncEq.WeakFEPair`
- Conclude analytic continuation + FE for `completedDedekindZeta`

This unlocks **both** `regulator_lower_bound_cm` (D3.2c) **and**
`dedekind_residue_upper_bound_cm` (D3.2b) once they can use `ζ_K(0)` and the
functional equation.

### PR 2: Stark-Tate formula for `ζ_K(0)`
- Define `ζ_K(0) = -h_K · R_K / w_K · …`
- Direct computation from FE + residue at s = 1

### PR 3: Friedman-style regulator lower bound
- Mellin integral positivity argument
- Concludes `R_K ≥ explicit_constant`

### PR 4: Chebotarev density (separate track, unlocks `chebotarev_fixed_Q`)
- Needs Dirichlet density on prime ideals
- Functional equation + nonvanishing of `dedekindZeta` on `Re s = 1`
- For *cyclotomic* K, `ζ_K = ∏ L(s, χ)` so Mathlib's nonvanishing for Dirichlet
  L-functions could be leveraged.
- For general K, needs full Hecke machinery.

### PR 5: Class field theory (UNLOCKS `gs_cm_tower`, very far)
- Idele class group, Artin reciprocity, Hilbert class field
- Pro-p group cohomology
- Golod–Shafarevich inequality
- This is a multi-PR effort tracked in Mathlib's roadmap.

## Bottom line

The shortest path to closing our off-path sorries (D3.2b + D3.2c) is:
**PR 1 → PR 2 → PR 3**, which is a coherent block of analytic number theory
formalization (Dedekind zeta + functional equation + special values + regulator
bound).

The proof-path sorries (D3.1.gs + D3.1.cheb) are separate efforts requiring
class field theory infrastructure.
