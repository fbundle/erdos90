# D3.2 — `class_num_bound_of_brd`: what we depend on

**Sorry location:** `Erdos90/NumberFieldDeep_GSTower.lean:137`
**Statement shape (Lean):**
```lean
lemma class_num_bound_of_brd
    (K : Type) [Field K] [NumberField K] [IsCMField K] [IsTotallyComplex K]
    (f : ℕ) (_hf : InfinitePlace.nrComplexPlaces K = f) (_hf1 : f ≥ 1)
    (rd_F : ℝ) (_hrd_F : 1 ≤ rd_F)
    (_h_K_from_brd_tower : True) :
    Real.log (Fintype.card (ClassGroup (𝓞 K)) : ℝ) / (f : ℝ) ≤
      2 * Real.log (2 * rd_F) := sorry
```

## ⚠️ The statement is currently mis-shaped

The hypothesis `_h_K_from_brd_tower : True` carries no information. The lemma as stated is
**false in general** — it claims that *every* CM totally complex field of degree ≥ 2
satisfies the bound for an *arbitrary* `rd_F ≥ 1`, which fails as soon as `rd(K) > rd_F`.

The intended hypothesis is `rd(K) ≤ rd_F`. The correct signature is:

```lean
lemma class_num_bound_of_brd
    (K : Type) [Field K] [NumberField K] [IsCMField K] [IsTotallyComplex K]
    (f : ℕ) (_hf : InfinitePlace.nrComplexPlaces K = f) (_hf1 : f ≥ 1)
    (rd_F : ℝ) (_hrd_F : 1 ≤ rd_F)
    (hrd_K : NumberField.rootDiscr K ≤ rd_F) :  -- ← was `True`
    Real.log (Fintype.card (ClassGroup (𝓞 K)) : ℝ) / (f : ℝ) ≤
      2 * Real.log (2 * rd_F) := sorry
```

**This is a 1-line fix** that should be made before any closure attempt. The callsite
(inside `brd_tower_data`) already has `rd(K) ≤ rd_F` from the BRD postulate; we just need
to thread it through.

## The mathematical theorem we depend on

**(Brauer–Siegel, qualitative form)** As `[K:ℚ] → ∞` with `K` ranging over a family of
number fields,
```
log(h_K · Reg(K)) / log √|disc K| → 1.
```

**(Louboutin 2000, explicit CM form)** For a CM number field `K` with totally real
subfield `K⁺ = K^c` (where `c` is complex conjugation) of degree `[K⁺:ℚ] = f`, write
`h_K = h⁻ · h⁺` (relative class number times class number of `K⁺`). Then for `K` with
`rd(K) ≥ 60` or so:

```
h⁻ · |d_{K/K⁺}|^{1/2} · Reg(K)/Reg(K⁺) ≤ explicit constant times (2π)^f · ∏ residues.
```

In particular, taking logs and dividing by `f`:
```
log(h⁻) / f ≤ log(rd(K)) + O(1)         ← Louboutin Theorem A
```

**(For the BRD tower)** In an unramified tower of CM fields above `F`, `rd(Kⱼ) = rd(F)`
exactly (root discriminant is constant). So `log(h_{Kⱼ}) / f_j ≤ log(rd(F)) + O(1)`.

Sawin's paper (Proposition 3.7, page 12 + Appendix A.13) packages this as:
```
h(K) ≤ max{2, rd(K)}^{C_class · [K:ℚ]}
```
for an absolute constant `C_class` (effectively constructable from Louboutin). Sawin
takes `C_class = 1`, which gives `log(h_K)/[K:ℚ] ≤ log(rd(K))`, hence
`log(h_K)/f ≤ 2 · log(rd(K)) ≤ 2 · log(rd_F)`.

Then `log(2 · rd_F) ≥ log(rd_F)`, so the headline bound `log(h_K)/f ≤ 2 · log(2 · rd_F)`
is what `class_num_bound_of_brd` postulates.

## Where the `2 ·` and `log(2 · rd_F)` come from

From Sawin's note (page 7, footnote): the `2` factor absorbs the `+ O(1)` slack in
Louboutin's estimate. The `log(2 · rd_F)` form (rather than `log(rd_F)`) ensures the
RHS is positive even when `rd_F = 1`, which the downstream `exists_admissible_family`
proof needs as part of threading `log_H > 0`.

## Decomposition into Mathlib-PR-shaped pieces

```lean
-- D3.2a: analytic class number formula — algebraic content
lemma classNumber_eq_residue_times_disc_over_regulator
    {K : Type*} [Field K] [NumberField K] :
    (Fintype.card (ClassGroup (𝓞 K)) : ℝ) =
      NumberField.dedekindZetaResidue K * Real.sqrt |NumberField.discr K| /
        (NumberField.regulator K * NumberField.torsionOrder K *
          2 ^ NumberField.nrRealPlaces K * (2 * Real.pi) ^ NumberField.nrComplexPlaces K) :=
  sorry
-- ← follows from `tendsto_sub_one_mul_dedekindZeta_nhdsGT` (in Mathlib!)
--   after rearranging; "essentially proved" modulo unfolding

-- D3.2b: upper bound on L(1, χ) for ring-class characters of CM K
lemma L_one_upper_bound_cm
    {K : Type*} [Field K] [NumberField K] [IsCMField K] [IsTotallyComplex K]
    (χ : RingClassCharacter K) :
    ‖LSeries.completed χ 1‖ ≤ Real.log (Real.exp 1 * NumberField.rootDiscr K) :=
  sorry
-- ← Louboutin 2000, Theorem 1; requires functional equation + Stechkin-style bound

-- D3.2c: regulator lower bound for CM fields
lemma regulator_lower_bound_cm
    {K : Type*} [Field K] [NumberField K] [IsCMField K] [IsTotallyComplex K] :
    NumberField.regulator K ≥ Real.exp (-(Module.finrank ℚ K : ℝ)) :=
  sorry
-- ← Zimmert / Friedman; involves unit-rank-1 case for CM
--   (for totally complex K with f ≥ 1, K⁺ has rank f-1)

-- D3.2d: chain a + b + c into the headline bound
lemma class_num_bound_of_brd
    (K : Type) [Field K] [NumberField K] [IsCMField K] [IsTotallyComplex K]
    (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f) (hf1 : f ≥ 1)
    (rd_F : ℝ) (hrd_F : 1 ≤ rd_F)
    (hrd_K : NumberField.rootDiscr K ≤ rd_F) :
    Real.log (Fintype.card (ClassGroup (𝓞 K)) : ℝ) / (f : ℝ) ≤
      2 * Real.log (2 * rd_F) :=
  -- Combine D3.2a (class no. = analytic formula),
  --       D3.2b (residue ≤ log(rd_K))^O(f),
  --       D3.2c (regulator ≥ exp(-O(f))),
  -- then divide by f, use log_four_r_div_pi_le_two_log_two_r
  sorry
```

Each piece has a clean citation:
- D3.2a — Dirichlet class number formula, Lang ANT VIII.2
- D3.2b — Louboutin 2000, `assets/louboutin_2000_class_number.pdf` Theorem 1
- D3.2c — Friedman 1989 ("Analytic formulas for the regulator…") or Zimmert 1981

## Realistic Mathlib gap

| Piece | Mathlib v4.30 status | Notes |
|---|---|---|
| `dedekindZetaResidue` definition | ✅ exists | `NumberField/DedekindZeta.lean` |
| `tendsto_sub_one_mul_dedekindZeta` (Dirichlet class number formula limit form) | ✅ exists | Same file |
| L-function functional equation for `ζ_K` | ❌ missing | Heavy: needs Hecke gamma factors |
| Upper bounds on `L(1, χ)` for Dirichlet characters | ❌ missing | Stechkin / Louboutin needs ζ analytic continuation past 1 |
| Regulator lower bound (Zimmert / Friedman) | ❌ missing | Builds on logarithmic-embedding lattice theory |
| Asymptotic ideal count (`# ideals norm ≤ N` ~ const·N) | ⚠️ asymptotic only | `Ideal/Asymptotics.lean` gives `→`, not uniform |

D3.2a is *closeable now* if we accept Mathlib's `tendsto_sub_one_mul_dedekindZeta`
as the analytic class number formula source. The proof would unfold the limit and
extract the explicit Dedekind class number formula.

D3.2b and D3.2c are honest Mathlib gaps. Estimated 2–4 months each. The L(1, χ)
bound alone requires building out L-function analytic continuation beyond `s > 1`,
the Hadamard product / functional equation, and Hurwitz-zeta-type bounds.

## Recommended near-term action

1. **Fix the `_h_K_from_brd_tower : True` placeholder** (5-line refactor).
2. **Split `class_num_bound_of_brd` into D3.2a/b/c/d**, with the analytic class number
   formula (D3.2a) attempted using Mathlib's existing `dedekindZetaResidue`.
3. **D3.2a may be closeable** without major Mathlib contributions; that would leave
   D3.2b and D3.2c as the only true gaps.

See `D32_analytic_class_number_mathlib_gap.md` for the Mathlib-side detailed survey.
