# D3.1 — `hmr_brd_cm_tower`: what we depend on

**Sorry location:** `Erdos90/NumberFieldDeep_GSTower.lean:116`
**Statement shape (Lean):** for each `ℓ ≥ 2`, exists `Q : ℕ` with `0 < Q`, `rd_F : ℝ` with
`1 ≤ rd_F` and `log rd_F ≤ ℓ · log ℓ`, and a callable `∀ (M t' : ℕ), ∃ K f sp, sp.Q = Q ∧ f ≥ M`
(K CM, totally complex, `nrComplexPlaces K = f`).

## The mathematical theorem we depend on

**(HMR 2021, Hajir–Maire–Ramakrishna)** Fix a prime ℓ. There exists a CM number field
`F` and an infinite ℓ-class-field tower `F = K₀ ⊂ K₁ ⊂ K₂ ⊂ …` such that:

- every `Kⱼ` is CM and totally complex
- `[Kⱼ : ℚ] → ∞`
- `rd(Kⱼ) = rd(F)` for all `j` (root discriminant is *constant* along an unramified tower,
  not just bounded)
- `F` can be chosen with `rd(F) < 84` (the explicit constant in HMR is ≈ 50.097 in their
  best example).

The construction (HMR §3) is: pick `F` of small rd satisfying the Golod–Shafarevich
inequality `r₂ < d²/4` on the ℓ-class-group cohomology, where `d = dim_{𝔽_ℓ} H¹(G, 𝔽_ℓ)`
and `r₂ = dim_{𝔽_ℓ} H²(G, 𝔽_ℓ)` for `G = Gal(K_S(F)/F)`. GS then forces the maximal
ℓ-extension unramified outside `S` to be infinite. Inside this infinite extension, take
the chain of fixed fields of an open chain of subgroups.

**(Chebotarev — Sawin's split-prime selection)** Given `F` from HMR and a target count
`t'` of split primes, Chebotarev density gives infinitely many rational primes `q` that
split completely in `F` (so a fortiori in every `Kⱼ`). Take any `t'` of them, set
`Q = q₁ · … · qₜ`. The split-prime data `sp` at level `Kⱼ` has `sp.Q = Q` fixed across `j`
because the *rational* primes are fixed; only the `𝓞_{Kⱼ}`-primes above them change.

The combined HMR + Chebotarev statement is what `hmr_brd_cm_tower` postulates.

## Decomposition into Mathlib-PR-shaped pieces

A single monolithic sorry hides four independent gaps. Recommended split (mirrors paper
structure):

```lean
-- D3.1a: pro-ℓ tower with bounded root discriminant (Golod–Shafarevich)
def gs_proℓ_tower_exists (ℓ : ℕ) (_hℓ : ℓ ≥ 2) :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F),
      ∃ (rd_F : ℝ), 1 ≤ rd_F ∧ Real.log rd_F ≤ (ℓ:ℝ) * Real.log ℓ ∧
      ∀ M, ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra F K)
            (_ : IsGalois F K),
        Module.finrank ℚ K ≥ M ∧ NumberField.rootDiscr K = rd_F := sorry

-- D3.1b: CM refinement of the tower
def cm_lift_of_gs_tower {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (tower : ∀ M, ∃ K …) :
    ∀ M, ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : IsCMField K')
            (_ : IsTotallyComplex K'),
      Module.finrank ℚ K' ≥ M ∧ NumberField.rootDiscr K' ≤ 2 * NumberField.rootDiscr F :=
  sorry

-- D3.1c: Chebotarev — infinitely many primes split completely in K
def exists_split_primes_in_tower {K : Type} [Field K] [NumberField K] :
    ∀ (S : Finset ℕ) (t' : ℕ),
      ∃ (qs : Finset ℕ), qs.card = t' ∧ Disjoint qs S ∧
        ∀ q ∈ qs, Nat.Prime q ∧ /* q splits completely in K/ℚ */ True := sorry

-- D3.1d: SplitPrimeData carrier (q's split in every level ⇒ structured sp)
-- Already mostly proved via splitPrimeData_from_prime_list
```

Each piece cites a different chapter of algebraic number theory:
- `gs_proℓ_tower_exists` ← Koch §11, HMR §3 / Hajir–Maire 2001
- `cm_lift_of_gs_tower` ← Washington Ch. 4, Milne CM Notes §3
- `exists_split_primes_in_tower` ← Lang ANT Ch. VIII, Neukirch §VII.13

## Realistic Mathlib gap

| Piece | What Mathlib v4.30 has | What is missing |
|---|---|---|
| Golod–Shafarevich inequality | nothing | pro-p cohomology, Frattini quotient, GS inequality |
| Maximal pro-ℓ extension unramified outside `S` | nothing | absolute Galois group, ramification filtration, `K_S(F)` |
| Hilbert class field / class field tower | nothing | class field theory (no Artin reciprocity!) |
| Chebotarev density | partial (Frobenius element exists) | the density theorem itself, Dirichlet density |
| CM refinement | `IsCMField`, `IsTotallyComplex` typeclasses | tensor-up-with-ℚ(i) construction, rd transfer |
| Root discriminant API | `NumberField.rootDiscr` | constancy along unramified extensions |

**Honest timeline to close in Mathlib:**
- pro-p cohomology + GS inequality: 6–12 months
- Class field theory (Artin reciprocity → HMR tower exists): 12–24 months
- Chebotarev density theorem: 6–12 months (depends on L-functions which `class_num_bound_of_brd`
  also needs — synergy)

A serious effort would be 2–3 person-years, not weeks.

## What we can do *right now* without closing the gap

1. **Refine the postulate signature** so it directly states the four pieces above, each
   as a `def … := sorry` with a docstring + literature citation. This makes the gap
   *legible* even if the proofs are far away.
2. **Sharpen the `rd_F` bound** in the postulate. Current bound is `log rd_F ≤ ℓ · log ℓ`,
   which is *much* weaker than HMR's explicit `rd_F < 84` (a constant). Tightening this is
   a no-cost win mathematically (HMR gives a strictly better bound), but downstream code
   uses `log rd_F ≤ ℓ · log ℓ` so we'd need to thread the constant version through.
3. **Stop treating Chebotarev as bundled with GS**. They are independent theorems; their
   proofs share L-function machinery but the *statements* don't. Splitting D3.1 into
   D3.1a (GS) + D3.1c (Chebotarev) makes the dependency on L-functions cleaner.

See `D31_class_field_theory_mathlib_gap.md` for the Mathlib-side detailed survey.
