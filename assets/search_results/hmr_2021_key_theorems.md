# HMR 2021 — key theorems we cite (with line refs to local tex)

**Paper:** Hajir, Maire, Ramakrishna, *"Cutting towers of number fields"*, Annales
Mathématiques du Québec **45** (2021), 321–345. arXiv:1901.04354.

**Local source:** `assets/hmr_2021_src/Cutting_towers_arxiv.tex`
**Local PDF:** `assets/hajir_maire_ramakrishna_2021.pdf`

## Theorem 1 (line 729) — Ihara's question / infinite splitting

> Let `K` be a number field, and `S` be a finite set of places of `K` coprime to `p`.
> Suppose that `d_p G_S > α_{K,S}` [the GS criterion]. Then there exists an infinite
> pro-`p` extension `K̃/K` in `K_S/K` for which the set of primes that split completely
> is infinite.

**This is the exact theorem we depend on for `hmr_brd_cm_tower`.** It gives:
- An infinite tower (`K̃/K`),
- Bounded ramification (`K̃ ⊂ K_S`, the maximal pro-`p` extension unramified outside `S`),
- Infinite completely-split set (the Q-primes for our SplitPrimeData).

**Proof (line 739)** uses Proposition `prop:cutting` (line 544) — the GS-cutting argument
with Zassenhaus filtration to control Frobenius depth.

## Definitions (line 712–717)

- **Root discriminant** of `K`: `rd_K := |Disc(K)|^{1/[K:ℚ]}`.
- **Root discriminant** of `L/K` (possibly infinite): `limsup_J |Disc(J)|^{1/[J:K]}`
  over `K ⊂ J ⊂ L` with `[J:K] < ∞`.
- **Asymptotically good** extension: root discriminant is finite.

## Proposition `prop:cutting` (line 544) — Golod–Shafarevich cutting

The technical heart. Roughly: given a GS polynomial `P_𝔓(t) = 1 - dt + rt²` with
`P_𝔓(t₀) < 0` for some `t₀ ∈ (0, 1)`, one can quotient `G_S` by Frobenius elements at
primes of high Zassenhaus depth (≥ `k' + i`) and still have an infinite pro-`p` group.

## §4 (line 860) — Martinet constants (root discriminant bounds)

`§4.1 Tame towers with finite ramification-exponent` (line 863) gives explicit
constructions of asymptotically good towers with small `rd`. Proposition (line 879,
`prop;exponent`) is the version we use for the BRD bound `log rd_F ≤ ℓ · log ℓ`.

For the CM case, the construction in HMR Theorem 4.2 (page 9 in arXiv) gives towers
with `rd ≈ 50.097` (totally complex), substantially better than the asymptotic
`exp(ℓ · log ℓ)` bound we currently use.

## How this maps to `hmr_brd_cm_tower`

Our Lean postulate bundles:
1. **GS existence** ← HMR §2 (line 391–612), Proposition `prop:cutting`.
2. **Asymptotic-good root discriminant bound** ← HMR §4 (line 860+).
3. **Fixed split primes Q across the tower** ← HMR §3 Theorem `theo:ihara` (line 729).
4. **CM refinement** ← Not in HMR directly; needs an extra base-change argument (tensor
   with ℚ(i) over the totally real subfield, plus the rd bound `rd(K) ≤ 2·rd(F)` from
   the conductor-discriminant formula).

## Quick line-grep cheat sheet

```bash
cd assets/hmr_2021_src
grep -n "theo:ihara\|theo:wilson\|prop:cutting\|prop;exponent" Cutting_towers_arxiv.tex
grep -nE "^\\\\(begin\\{(theorem|prop|cor|lemma|coro)|section)" Cutting_towers_arxiv.tex
```

The paper is ~50 pages (Cutting_towers_arxiv.tex line count ≈ 2000); sections relevant
for D3.1 are §2, §3, §4.
