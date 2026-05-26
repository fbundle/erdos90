# D3.2 — Mathlib gap for analytic class number + L-function bounds

Survey of `vendor/mathlib4/Mathlib/` (v4.30.0-rc2 / master-2026-05-24) for the
infrastructure required to close `class_num_bound_of_brd`.

## What Mathlib has (good news)

### Dedekind zeta function
- `Mathlib/NumberTheory/NumberField/DedekindZeta.lean` (88 lines)
  - `dedekindZeta K s := LSeries (fun n ↦ Nat.card {I : Ideal (𝓞 K) // absNorm I = n}) s`
  - `dedekindZetaResidue K = (2^r₁ · (2π)^r₂ · regulator K · classNumber K) /
                              (torsionOrder K · √|discr K|)`
  - `tendsto_sub_one_mul_dedekindZeta_nhdsGT` : `(s - 1) · ζ_K(s) → dedekindZetaResidue K`
    as `s → 1⁺`. **This is the Dirichlet class number formula in limit form.**

### Ideal counting asymptotics
- `Mathlib/NumberTheory/NumberField/Ideal/Asymptotics.lean` (162 lines)
  - `tendsto_norm_le_div_atTop` : `Nat.card {I // absNorm I ≤ s} / s → dedekindZetaResidue K`
    as `s → ∞`. (Asymptotic ideal count.)
  - `tendsto_norm_le_and_mk_eq_div_atTop` : refined version per class.

### Minkowski-bound infrastructure
- `Mathlib/NumberTheory/NumberField/ClassNumber.lean`
  - `exists_ideal_in_class_of_norm_le` : every ideal class has a representative with norm
    ≤ `M K` (where `M K` is the local notation for the Minkowski bound).
- `Mathlib/NumberTheory/NumberField/Discriminant/Basic.lean`
  - `NumberField.rootDiscr K = |discr K|^(1/[K:ℚ])`.

### L-series infrastructure
- `Mathlib/NumberTheory/LSeries/` — `LSeries`, `LSeries.completed`, `riemannZeta`,
  `dirichletLSeries` (analytic continuation, functional equation for `ζ` and Dirichlet L's).

## What Mathlib is MISSING (the blockers)

### 1. Functional equation for `dedekindZeta`

The Dedekind zeta has a functional equation
```
Λ_K(s) := |d_K|^{s/2} · Γ_ℝ(s)^{r₁} · Γ_ℂ(s)^{r₂} · ζ_K(s) = Λ_K(1-s)
```
where `Γ_ℝ(s) = π^{-s/2} Γ(s/2)` and `Γ_ℂ(s) = 2 (2π)^{-s} Γ(s)`. Mathlib has the
functional equation for `riemannZeta` and `dirichletLSeries` (the rank-1 case), but
not for general Dedekind zeta. **Estimated effort to formalize: 4–6 months.**

This is what `class_num_bound_of_brd` ultimately needs for the upper bound on the
residue, because Louboutin's bound is derived via the functional equation evaluated
in a left-of-the-critical-strip region.

### 2. Upper bound on `L(1, χ)` for ring-class characters

For a ring class character `χ` of `K` of conductor `𝔣`, Louboutin proves
```
|L(1, χ)| ≤ ½ · log(c_K · |N(𝔣)| · rd(K)) + small
```
This bound is the **technical heart** of Brauer–Siegel quantitative. Mathlib has:
- The Riemann zeta partial-sums bound `Re ζ(1+ε) ≤ 1/ε + γ` (Euler–Mascheroni).
- Nothing for Hecke / Dirichlet characters at `s=1` beyond non-vanishing.

The bound needs (a) functional equation, (b) Phragmén–Lindelöf type interpolation,
(c) Stark / Stechkin partial-sum control. **Estimated effort: 4–8 months.**

### 3. Regulator lower bound (Zimmert / Friedman)

`Reg(K) ≥ const^{[K:ℚ]}` for `const > 1/e` — this is Zimmert's analytic regulator
bound. Mathlib has only `Reg(K) > 0` (positivity). The proof goes via the
Stark–Friedman analytic formula `Reg(K) = (residue of certain logarithmic
Eisenstein series at s=1)` plus Friedman's Mellin-style integral bound.

Mathlib has the regulator `NumberField.regulator` and the logarithmic embedding
`NumberField.Units.logEmbedding`, but neither the Friedman analytic formula nor the
lower bound. **Estimated effort: 3–6 months.**

### 4. Effective ideal count (not just asymptotic)

`Ideal/Asymptotics.lean` proves the *limit* `# ideals(N) / N → c_K`. We need a
*uniform* bound `# ideals(N) ≤ C(K) · N` for all `N` (or at least for `N ≥ N₀(K)`).

The current `Mathlib4_Extra.card_ideals_of_norm_le_bound` in this repo proves
`# ideals(N) ≤ 2^((N!)^[K:ℚ])` (doubly exponential). This is far from `O(N)`.

A genuine `O(N)` bound (or even `O(N log^{n-1} N)`) requires either:
- Hermite normal form for sublattices of `ℤ^n` (≈ 4–6 months of Mathlib work), or
- The Dedekind zeta partial-sum + Tauberian argument (overlaps with D3.2a's
  unfolding of the limit; ≈ 2–3 months).

This is the cleanest "Mathlib PR opportunity" of the four pieces — pure number
theory with no class field theory dependency.

### 5. Brauer–Siegel "lower bound" (for sharpness, not strictly needed)

Brauer–Siegel asserts both `log(hR) / log √|d| → 1` (upper *and* lower). For
`class_num_bound_of_brd` only the upper bound matters; the lower bound (Siegel
1935) is not needed.

## What's *closeable now* without major Mathlib contributions

**D3.2a is plausibly closeable** by unfolding the existing
`tendsto_sub_one_mul_dedekindZeta_nhdsGT` into an algebraic equation between class
number, residue, regulator, and discriminant:

```
classNumber K = dedekindZetaResidue K · √|discr K| ·
                  torsionOrder K / (2^r₁ · (2π)^r₂ · regulator K)
```

This is just rearranging the definition of `dedekindZetaResidue`. It's an algebraic
identity (no analysis); the limit-form theorem already gives us the value.

**Estimated effort for D3.2a alone: 1–2 weeks** of Mathlib-style work.

After D3.2a is closed, `class_num_bound_of_brd` reduces to:
```
log(classNumber K) / f ≤ log(dedekindZetaResidue K) / f
                       + (1/2) log|discr K| / f
                       - log(regulator K) / f
                       + O(1) / f
```
The middle term `(1/2) log|discr K| / f = log(rd(K))` is exact. The remaining
pieces (residue upper bound, regulator lower bound) are the real gaps.

## Recommended near-term action

1. **Fix the statement** of `class_num_bound_of_brd` (the `True` hypothesis bug).
2. **Attempt D3.2a closure** (analytic class number formula as algebraic identity)
   as a near-term Mathlib contribution — likely tractable.
3. **Frame D3.2b (L(1,χ) bound) as a Mathlib-PR opportunity**: it's a pure analysis
   result (Louboutin 2000) with no class-field-theory entanglement, unlike D3.1.
4. **Push for `O(N)` ideal count in Mathlib**: independently valuable for many number
   theory formalizations, and would also tighten this project's
   `Mathlib4_Extra/ClassNumberBound.lean` from doubly-exponential to polynomial.

## Bottom line

D3.2 is harder than D3.1 in *terms of L-function depth*, but **the pieces are
independent of class field theory**, making it a more attractive Mathlib target.
Plausible 6–12-month roadmap with a focused number-theory PR push.
