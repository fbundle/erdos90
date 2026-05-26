/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Erdos90.Mathlib4_Extra.UnramifiedDiscriminant

/-!
# Chebotarev density and Ihara's theorem — Mathlib-PR-shape stub

The `chebotarev_fixed_Q` sorry in `Erdos90/NumberFieldDeep_GSTower.lean` asks
for: given a root-discriminant bound `rd_F`, there's a fixed product of
rational primes `Q` such that for every CM totally complex `K` with
`rootDiscr K ≤ rd_F` and every `t'`, there's a `SplitPrimeData K (t'·f)`
with `sp.Q = Q`.

The mathematical content: in an HMR-style **infinite pro-`ℓ` tower** `K_S(F)/F`
(maximal pro-`ℓ` extension of base field `F`, unramified outside a finite set
`S`), there are infinitely many rational primes splitting completely in
*every* level of the tower.  Pick `t'` of them, multiply: gives a fixed `Q`.

This is **Ihara's theorem** (1986), strictly stronger than Chebotarev density.
Chebotarev gives split primes in a SINGLE Galois extension; Ihara gives split
primes that persist in an INFINITE tower.

## Why `chebotarev_fixed_Q` is not closed by persistence + Chebotarev

A naive attempt:
1. By Chebotarev, pick `t'` primes splitting in the base `F`.
2. By "split persistence under unramified extensions", these stay split in
   every level of the unramified tower.

Step 2 is FALSE in general.  "Split completely" requires both
`ramificationIdx = 1` AND `inertiaDeg = 1`.  Unramified extensions
preserve `ramificationIdx = 1` (by `not_dvd_differentIdeal_iff` + tower
formula), but the residue field extension can have nontrivial degree —
so `inertiaDeg` can grow.

The actual HMR / Ihara argument uses that in a **pro-`ℓ` extension**,
the inertia/Frobenius operates by `ℓ`-power Galois elements; combined with
the structure of the `S`-ray class field tower, one gets persistence of
split primes via Frobenius behavior.  This is genuinely a deeper result.

## What this file provides

* `chebotarev_density_postulate` — Chebotarev density theorem, stated cleanly:
  for any number field, the set of split rational primes is infinite.
  (Mathlib v4.30 has this for cyclotomic fields only.)
* `ihara_split_primes_postulate` — Ihara's theorem: for the HMR pro-`ℓ`
  tower, there are infinitely many fixed split primes across the tower.
* Documented attempt at decomposing `chebotarev_fixed_Q` via these.

## What's in Mathlib v4.30

- `Ideal.ramificationIdx_algebra_tower` (PROVED, see RamificationInertia/Ramification.lean:337)
- `Ideal.inertiaDeg_algebra_tower` (PROVED, see RamificationInertia/Inertia.lean:175)
- `IsCyclotomicExtension.Rat.zeta_split` (PROVED, cyclotomic Chebotarev) — only
  for `ℚ(ζ_n)/ℚ`, not general number fields.
- General Chebotarev density: **ABSENT**.  Requires L-function continuation.
- Ihara 1986: **ABSENT**.  Requires Chebotarev + pro-p group theory.

## References

- HMR 2021 §3, `theo:ihara` line 729 of `assets/hmr_2021_src/Cutting_towers_arxiv.tex`.
- Ihara, *How many primes decompose completely in an infinite unramified
  Galois extension of a global field?* J. Math. Soc. Japan **35** (1983) 693-709.
- Standard CFT reference for Chebotarev density: Neukirch, *Algebraic Number
  Theory*, VII §13.
-/

namespace NumberField

open NumberField

/-- **Chebotarev density theorem** (labelled postulate).

For any number field `K`, infinitely many rational primes split completely
in `𝓞 K`.  More precisely: the set `{q : ℕ | q.Prime ∧ q splits completely in K}`
is infinite.

This is the simplest form of the Chebotarev density theorem (the trivial-conjugacy
class case).  Mathlib v4.30 has analogous results for `ℚ(ζ_n)/ℚ` only.

Cite: Neukirch, *Algebraic Number Theory*, Chapter VII §13.  Not in Mathlib v4.30. -/
def chebotarev_density_postulate (K : Type*) [Field K] [NumberField K] :
    {q : ℕ | q.Prime ∧
      ∃ (P : Ideal (𝓞 K)), P.IsPrime ∧ P ≠ ⊥ ∧
        Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) P = 1 ∧
        Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) P = 1}.Infinite := sorry

/-- **Ihara's theorem** (labelled postulate).

For each base field `F` (number field) and each prime `ℓ ≥ 2`, the maximal
pro-`ℓ` extension `K_∞ = K_S(F)/F` (unramified outside a finite set `S`)
has the property that infinitely many primes split completely in *every*
finite sub-extension.

This is Ihara 1983/1986: in an asymptotically good pro-`ℓ` extension, there
are positive-density "completely split" primes that persist through the tower.

Cite: HMR 2021 line 729 `theo:ihara`; Ihara, *How many primes decompose...*,
J. Math. Soc. Japan 35 (1983) 693-709.  Not in Mathlib v4.30. -/
def ihara_split_primes_postulate
    (F : Type*) [Field F] [NumberField F] [IsCMField F] [IsTotallyComplex F]
    (ℓ : ℕ) (_hℓ : ℓ ≥ 2) (rd_F : ℝ) (_h_rd : 1 ≤ rd_F)
    (_h_rd_F : rootDiscr F ≤ rd_F) :
    ∃ (S_split : Set ℕ), S_split.Infinite ∧
      (∀ q ∈ S_split, q.Prime) ∧
      ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [IsTotallyComplex K]
        (_ : Algebra F K),
        rootDiscr K ≤ rd_F →
        (∀ (P : Ideal (𝓞 K)) [P.IsPrime], P ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 F) P) →
        ∀ q ∈ S_split, ∃ (P : Ideal (𝓞 K)), P.IsPrime ∧ P ≠ ⊥ ∧
          Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) P = 1 ∧
          Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) P = 1 := sorry

/-! ## Why we don't directly use these to close `chebotarev_fixed_Q`

The existing `chebotarev_fixed_Q` quantifies over **all** CM totally complex
`K` with `rootDiscr K ≤ rd_F`, not just tower levels above a fixed base.
This over-states what HMR/Ihara provide.

For our proof-path, the statement is consumed by `hmr_brd_cm_tower` which
ALSO has access to a base field `F` (via `gs_cm_tower`), but the current
signature of `chebotarev_fixed_Q` doesn't expose that base.  Either:

1. **Refactor**: change `chebotarev_fixed_Q` to take a base field `F` as
   input (matching Ihara's signature), and have the caller supply it.
2. **Strengthen via Hermite–Minkowski**: there are finitely many number
   fields with `rootDiscr K ≤ rd_F` (Hermite–Minkowski).  Apply Chebotarev
   to each, intersect the split-prime sets.  Requires:
   * Hermite–Minkowski (not in Mathlib v4.30).
   * `chebotarev_density_postulate` (above).

Both routes leave `chebotarev_fixed_Q` blocked on Mathlib gaps.  The cleanest
future direction is option (1) — but that requires propagating the base
field through `gs_cm_tower → hmr_brd_cm_tower`, which is a larger refactor.
-/

end NumberField
