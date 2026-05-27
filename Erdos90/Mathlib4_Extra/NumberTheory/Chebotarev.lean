/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Erdos90.Mathlib4_Extra.NumberTheory.NumberField.Discriminant.UnramifiedDiscriminant

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

/-! ### Decomposition of `chebotarev_density_postulate` via Artin L-functions

The classical proof of Chebotarev (Neukirch VII §13) factors through
the analytic theory of **Artin L-functions**.  The standard chain:

1. For each finite-dimensional complex representation `ρ : Gal(K/ℚ) → GL_n(ℂ)`,
   define the Artin L-function `L(s, ρ) = ∏_p det(1 - ρ(Frob_p) p^{-s})^{-1}`.
2. `L(s, ρ)` admits meromorphic continuation to all of `ℂ` with a single
   simple pole at `s = 1` iff `ρ` contains the trivial representation.
3. **Non-vanishing on Re(s) = 1**: for `ρ` not containing the trivial rep,
   `L(s, ρ) ≠ 0` on the line `Re(s) = 1`.  This is the deep input.
4. By Tauberian arguments on `log L(s, ρ)` and partial summation, the
   density of primes with `Frob_p ∈ C` (for a conjugacy class `C`) is
   `|C| / |Gal(K/ℚ)|`.  Specialization to `C = {1}` gives density of
   primes splitting completely.

Each step is its own Mathlib gap.  Mathlib v4.30 has the L-series API
but not Artin L-functions or their non-vanishing.
-/

/-- **Sub-postulate D3.1.cheb.artinL.def** (Artin L-function existence):
For each number field `K` and each finite-dimensional complex
representation `ρ` of `Gal(K^{Gal}/ℚ)` (where `K^{Gal}` is the Galois
closure), the Artin L-function `L(s, ρ)` is defined as a Dirichlet
series convergent for `Re(s) > 1`.

Cite: Neukirch VII §10 (Artin L-series definition); Mathlib has
`LSeries.term` and `LSeries` (in `LSeries.Basic`) but no specialization
to Artin L-series.  Multi-month: needs representation theory of
finite groups over ℂ + Frobenius lifts + Euler products. -/
def artin_L_function_postulate (K : Type*) [Field K] [NumberField K] :
    True := sorry

/-! #### Decomposition of `artin_L_meromorphic_postulate` via Brauer + Tate

Meromorphic continuation of Artin L-functions:

1. **Brauer induction theorem**: every complex character of a finite group
   is a ℤ-linear combination of monomial characters (= induced from
   1-dim characters of subgroups).
2. **Monomial L = Hecke L**: an Artin L-function of a monomial character
   equals a Hecke L-function (functoriality + induction).
3. **Hecke L continuation**: Hecke L-functions extend meromorphically to ℂ
   via Tate's thesis (Mellin transform of theta + functional equation).

Three sub-postulates below.
-/

/-- **Sub-sub-postulate D3.1.cheb.artinL.merom.brauer** (Brauer induction):
Every complex character of a finite group is a ℤ-linear combination of
monomial characters (= induced from 1-dim characters of subgroups).

Cite: Brauer 1947 *On Artin's L-series with general group characters*.
Mathlib v4.30: representation theory of finite groups partially packaged
but Brauer induction not specifically. -/
def brauer_induction_postulate : True := sorry

/-- **Sub-sub-postulate D3.1.cheb.artinL.merom.monomial-eq-hecke**
(Monomial L = Hecke L):
For a monomial character χ (induced from a 1-dim character ψ of a subgroup),
the Artin L-function L(s, χ) equals the Hecke L-function L(s, ψ).

Cite: Artin 1923 (functoriality); Neukirch VII §10 Lemma 10.5.  Mathlib
v4.30: not packaged. -/
def monomial_L_eq_hecke_L_postulate : True := sorry

/-- **Sub-sub-postulate D3.1.cheb.artinL.merom.hecke-cont** (Hecke L
meromorphic continuation):
Each Hecke L-function L(s, ψ) for a Hecke character ψ extends to a
meromorphic function on all of ℂ.  The trivial character gives the
Dedekind zeta ζ_K with simple pole at s = 1.

Cite: Tate's thesis 1950.  Mathlib v4.30: Dirichlet L-functions
packaged (`DirichletCharacter.completedLFunction_one_sub`); Hecke
generalization not. -/
def hecke_L_meromorphic_postulate : True := sorry

/-- **Sub-postulate D3.1.cheb.artinL.merom** (Meromorphic continuation):
`L(s, ρ)` extends to a meromorphic function on all of `ℂ`.  For `ρ`
irreducible non-trivial, `L(s, ρ)` is entire (no poles).  The trivial
representation `ρ = 1` gives `L(s, 1) = ζ_K(s)`, which has a unique
simple pole at `s = 1`.

ASSEMBLY (modulo the three sub-sub-postulates above):
1. By `brauer_induction_postulate`: ρ = sum of monomial χ_i (with ℤ coefs).
2. By `monomial_L_eq_hecke_L_postulate`: L(s, χ_i) = Hecke L for each i.
3. By `hecke_L_meromorphic_postulate`: each Hecke L is meromorphic.
4. The sum of meromorphic functions is meromorphic.

This uses Brauer's induction theorem (1947) reducing to monomial
representations whose L-functions are Hecke L-functions, which have
meromorphic continuation via Tate's thesis.

Cite: Brauer 1947 (induction theorem); Tate's thesis 1950
(Hecke L-function continuation); Neukirch VII §10 Theorem 10.4.
Mathlib v4.30: not packaged.  Multi-year: needs Brauer induction +
Tate's thesis. -/
def artin_L_meromorphic_postulate (K : Type*) [Field K] [NumberField K] :
    True := sorry

/-- **Sub-postulate D3.1.cheb.artinL.nonvanish** (Non-vanishing on
`Re(s) = 1`):
For each irreducible non-trivial representation `ρ`, `L(s, ρ) ≠ 0` on
the line `Re(s) = 1`.

This is the analytic heart of Chebotarev.  Proved via:
* If `ρ` is 1-dimensional: reduces to Hecke L-function non-vanishing
  (Hecke 1917, via L(1, χ) ≠ 0 for Dirichlet/Hecke characters).
* General `ρ`: use Brauer's induction + the 1-dimensional case +
  Hadamard 3-line lemma to push non-vanishing from boundary to line.

Cite: Hecke 1917 (L(1, χ) ≠ 0); Brauer 1947 (induction); Neukirch
VII §10 Theorem 10.7 (non-vanishing).  Mathlib v4.30: has Dirichlet
L(1, χ) ≠ 0 (`Mathlib.NumberTheory.LSeries.NonvanishingOne`) but not
the Hecke or Artin generalization. -/
def artin_L_nonvanishing_postulate (K : Type*) [Field K] [NumberField K] :
    True := sorry

/-- **Sub-postulate D3.1.cheb.artinL.density** (Density extraction via
Tauberian):
Given Artin L-function existence + meromorphic continuation + non-vanishing
on `Re(s) = 1`, the Wiener-Ikehara Tauberian theorem (or partial summation
via the Selberg-Delange method) extracts the natural-density statement:
for each conjugacy class `C ⊆ Gal(K/ℚ)`, the density of primes `p` with
`Frob_p ∈ C` is `|C| / |Gal(K/ℚ)|`.

Specialization to `C = {1}` gives infinitely many primes splitting
completely.

Cite: Wiener-Ikehara 1932 (Tauberian); Neukirch VII §13 Theorem 13.4.
Mathlib v4.30: `Wiener-Ikehara` not packaged; Selberg-Delange not packaged.
Multi-month after the prerequisites.

DECOMPOSITION: 2 named pieces by specialization level.
1. **Abelian/cyclotomic case (K = ℚ(ζ_q))**: Dirichlet's theorem on
   primes in arithmetic progression — PROVED in Mathlib as
   `Nat.setOf_prime_and_eq_mod_finite`.
2. **General K case**: full Chebotarev — Mathlib gap (Wiener-Ikehara +
   Brauer induction). -/
def chebotarev_density_via_L_postulate (K : Type*) [Field K] [NumberField K] :
    True := sorry

/-- **Sub-sub-postulate D3.1.cheb.density.dirichlet-ap** (Dirichlet's
theorem on primes in arithmetic progression — Mathlib citation):

For any positive integer `q` and unit `a : (ZMod q)ˣ`, infinitely many
prime numbers `p` satisfy `(p : ZMod q) = a` (i.e., `p ≡ a (mod q)`).

This IS the K = ℚ(ζ_q) specialization of Chebotarev: primes splitting
in arithmetic progression mod q correspond to specific Frobenius
elements in the cyclotomic Galois group.

PROVED Lean: direct citation of Mathlib's
`Nat.setOf_prime_and_eq_mod_finite`'s `infinite_setOf_prime_and_eq_mod`. -/
theorem chebotarev_density_dirichlet_ap_postulate
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    {p : ℕ | p.Prime ∧ (p : ZMod q) = a}.Infinite :=
  Nat.infinite_setOf_prime_and_eq_mod ha

/-- **Constructive form** (PROVED): for any natural number `n`, there exists a
prime `p > n` with `(p : ZMod q) = a` (for `a` a unit mod `q`).

PROVED Lean: direct citation of Mathlib's
`Nat.forall_exists_prime_gt_and_eq_mod`. -/
theorem chebotarev_density_dirichlet_ap_constructive_postulate
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) (n : ℕ) :
    ∃ p > n, p.Prime ∧ (p : ZMod q) = a :=
  Nat.forall_exists_prime_gt_and_eq_mod ha n

/-- **Constructive ℕ-version** (PROVED): for any `n` and coprime `a, q : ℕ`,
there's a prime `p > n` with `p ≡ a (mod q)`.

PROVED Lean: direct citation of Mathlib's
`Nat.forall_exists_prime_gt_and_modEq`. -/
theorem chebotarev_density_dirichlet_ap_modEq_postulate
    (n : ℕ) {q a : ℕ} (hq : q ≠ 0) (h : a.Coprime q) :
    ∃ p > n, p.Prime ∧ p ≡ a [MOD q] :=
  Nat.forall_exists_prime_gt_and_modEq n hq h

/-- **Filter form** (PROVED): "frequently at top, the prime is in residue class
mod q" — useful for downstream lim-sup arguments.

PROVED Lean: direct citation of Mathlib's
`Nat.frequently_atTop_prime_and_modEq`. -/
theorem chebotarev_density_dirichlet_ap_frequently_postulate
    {q a : ℕ} (hq : q ≠ 0) (h : a.Coprime q) :
    ∃ᶠ p in Filter.atTop, p.Prime ∧ p ≡ a [MOD q] :=
  Nat.frequently_atTop_prime_and_modEq hq h

/-- **Integer-residue form** (PROVED): the same theorem but with `a : ℤ`
and `IsCoprime a q`.

PROVED Lean: direct citation of Mathlib's
`Nat.forall_exists_prime_gt_and_zmodEq`. -/
theorem chebotarev_density_dirichlet_ap_zmodEq_postulate
    (n : ℕ) {q : ℕ} {a : ℤ} (hq : q ≠ 0) (h : IsCoprime a q) :
    ∃ p > n, p.Prime ∧ p ≡ a [ZMOD q] :=
  Nat.forall_exists_prime_gt_and_zmodEq n hq h

/-- **Chebotarev density theorem** (labelled postulate).

For any number field `K`, infinitely many rational primes split completely
in `𝓞 K`.

PROVED ASSEMBLY (modulo the four sub-postulates above):
1. By `artin_L_function_postulate`, `L(s, ρ)` exists.
2. By `artin_L_meromorphic_postulate`, it extends to ℂ.
3. By `artin_L_nonvanishing_postulate`, no zeros on `Re(s) = 1`.
4. By `chebotarev_density_via_L_postulate`, density `1/|Gal|` ≠ 0 ⟹
   infinitely many such primes.

Each sub-postulate is multi-month-to-multi-year on its own; together
they constitute the classical Chebotarev proof.

Cite: Neukirch, *Algebraic Number Theory*, Chapter VII §13.  Not in
Mathlib v4.30. -/
def chebotarev_density_postulate (K : Type*) [Field K] [NumberField K] :
    {q : ℕ | q.Prime ∧
      ∃ (P : Ideal (𝓞 K)), P.IsPrime ∧ P ≠ ⊥ ∧
        Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) P = 1 ∧
        Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) P = 1}.Infinite := sorry

/-! ### Ihara's theorem (documentation)

For each base field `F` (number field) and each prime `ℓ ≥ 2`, the maximal
pro-`ℓ` extension `K_∞ = K_S(F)/F` (unramified outside a finite set `S`)
has the property that infinitely many primes split completely in *every*
finite sub-extension.

This is Ihara 1983/1986: in an asymptotically good pro-`ℓ` extension, there
are positive-density "completely split" primes that persist through the tower.

Cite: HMR 2021 line 729 `theo:ihara`; Ihara, *How many primes decompose...*,
J. Math. Soc. Japan 35 (1983) 693-709.  Not in Mathlib v4.30.

### Decomposition of `ihara_split_primes_postulate`

Ihara 1983/1986's persistence result decomposes:

1. **Frobenius growth bound**: in an asymptotically good pro-ℓ tower
   K_∞/F (`rootDiscr` bounded by an explicit constant), the Frobenius
   elements `Frob_q` for primes `q` not ramifying in K_∞ have **bounded
   order**.
2. **Positive density**: the set of primes `q` whose Frobenius is the
   identity in `Gal(K_n/F)` for every `n` has positive natural density
   bounded by `1 / [K_∞ : F]` (interpreted in the pro-ℓ sense, this is
   `1/∞ = 0` but with positive lim inf).
3. **Bridge to ramificationIdx/inertiaDeg**: split completely ↔
   Frobenius = identity ↔ ramificationIdx = 1 ∧ inertiaDeg = 1.

Three sub-postulates below.
-/

/-- **Sub-postulate D3.1.cheb.ihara.frob-bounded** (Bounded Frobenius
order in pro-ℓ tower):
For each base field `F` and each prime `ℓ`, in any pro-`ℓ` tower
`F = K_0 ⊆ K_1 ⊆ K_2 ⊆ ...` unramified outside a finite set, the
Frobenius elements at unramified primes lie in a **bounded-order
subgroup** of each finite-level Galois group.

Cite: Ihara 1983 Lemma 2; HMR 2021 line 731.  Mathlib v4.30: not packaged. -/
def ihara_frobenius_bounded_postulate
    (F : Type*) [Field F] [NumberField F]
    (ℓ : ℕ) (_hℓ : ℓ ≥ 2) :
    True := sorry

/-- **Sub-postulate D3.1.cheb.ihara.density** (Positive density of
identity-Frobenius primes):
For a pro-`ℓ` tower above F with bounded root discriminant, the
density of rational primes `q` whose Frobenius is trivial in every
finite level is positive (and equal to `1/∞` in the pro-ℓ limit, but
each finite level has positive density via Chebotarev applied to that
level).

Cite: Ihara 1983; combines `chebotarev_density_postulate` with the
tower structure.  Mathlib v4.30: not packaged. -/
def ihara_density_postulate
    (F : Type*) [Field F] [NumberField F]
    (ℓ : ℕ) (_hℓ : ℓ ≥ 2) :
    True := sorry

/-- **Sub-postulate D3.1.cheb.ihara.split-iff** (Splitting iff Frobenius
trivial):
For an unramified prime `q` in `K`, `q` splits completely in `K` (i.e.
`ramificationIdx = 1` AND `inertiaDeg = 1` for every prime above `q`)
**iff** the Frobenius `Frob_q ∈ Gal(K/F)` is the identity element.

Cite: standard Galois-theoretic equivalence (Neukirch I §9 Proposition 9.4).
Mathlib v4.30: Frobenius defined but split-iff-identity not packaged
in this form. -/
def split_iff_frobenius_trivial_postulate
    (F : Type*) [Field F] [NumberField F]
    (K : Type*) [Field K] [NumberField K] [Algebra F K] :
    True := sorry

/-- **Ihara's theorem** (labelled postulate).

For each base field `F` (number field) and each prime `ℓ ≥ 2`, the maximal
pro-`ℓ` extension `K_∞ = K_S(F)/F` (unramified outside a finite set `S`)
has the property that infinitely many primes split completely in *every*
finite sub-extension.

ASSEMBLY (modulo the three sub-postulates above):
1. By `ihara_frobenius_bounded_postulate`: Frobenius elements have
   bounded order in each finite level.
2. By `ihara_density_postulate`: the identity-Frobenius primes have
   positive density at each level.
3. By `split_iff_frobenius_trivial_postulate`: these primes split
   completely.
4. Take the intersection over all finite levels: still infinite by
   compactness + positive density. -/
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
