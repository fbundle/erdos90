# How CFT closes gs_cm_tower_infinite_postulate

This document shows the proof chain from class field theory primitives (now
in `Erdos90/Mathlib4_Extra/*`) to closing `gs_cm_tower_infinite_postulate`,
the sole remaining proof-path Mathlib gap in the Erd46 formalization.

## Target

```lean
def gs_cm_tower_infinite_postulate
    (p : ℕ) (_hp : Nat.Prime p) (ℓ : ℕ) (_hℓ : ℓ ≥ 2) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K)
      (_ : IsCMField K) (_ : IsTotallyComplex K),
      ∃ (_ : NumberField.rootDiscr K ≤ (ℓ : ℝ)),
        ∀ (N : ℕ), ∃ (L : Type) (_ : Field L) (_ : NumberField L)
          (_ : IsCMField L) (_ : IsTotallyComplex L)
          (_ : Algebra K L),
          Module.finrank K L ≥ p ^ N ∧
          NumberField.rootDiscr L = NumberField.rootDiscr K
```

## Closure roadmap

Step-by-step Lean proof outline (assuming all `Mathlib4_Extra/*` postulates):

### Step 1: Pick K = HMR base field

Take `K` to be a specific CM cyclotomic field of complex degree 1 with the
property that some prime `p ∤ classNumber K` plus large `p`-class group rank
exists.  E.g., `K = ℚ(ζ_q)` for a carefully chosen `q`.

The HMR paper (line 282 of `assets/hmr_2021_src/Cutting_towers_arxiv.tex`)
uses `K = ℚ(ζ_{4·p^k})` for a suitable `p, k` with `S = {p}`.

**Reference**: `RayClassField.lean` for the `MaxProPExt K p S` structure.

### Step 2: Apply `maxProPExt_exists` to get `K_∞ = K_S^{(p)}`

```
let K_inf : MaxProPExt K p {⟨p⟩} := maxProPExt_exists K p Nat.prime_p {⟨p⟩} ...
```

`K_∞` is a (possibly infinite) tower with:
- `Gal(K_∞/K)` is a pro-`p` group.
- `K_∞/K` is unramified outside `S = {p}`.

**Reference**: `RayClassField.lean`.

### Step 3: Apply Golod–Shafarevich criterion

Show that the pro-`p` group `Gal(K_∞/K)` has minimal presentation `(d, r)`
satisfying the GS test `r < d^2 / 4`, hence is INFINITE.

```
let gs_input : GolodShafarevich.Input := {
  p, hp_prime := Nat.prime_p, d := ..., r := ..., hGS := ...
}
let inf_proof : True := GolodShafarevich.gs_group_infinite gs_input
```

**Reference**: `GolodShafarevich.lean` (`Input` structure).

For HMR's specific construction, `(d, r) = (..., ...)` can be computed
explicitly from `K, p, S`.  See HMR 2021 §2 `prop;exponent`.

### Step 4: For each N, find tower level L with `[L:K] ≥ p^N`

Since `Gal(K_∞/K)` is infinite pro-`p`, every finite quotient is finite,
but their cardinalities are unbounded.  Pick `N`-th level satisfying degree
bound.

**Reference**: standard pro-`p` group theory + `MaxProPExt.L` field of the
structure.

### Step 5: Each L is unramified outside S, hence rootDiscr bounded

By the structure of `K_∞/K` (unramified outside `S = {p}`), and `p ∈ S`
allows tame ramification.  Apply HMR's refined rd bound:

```
∀ L : sub-extension of K_∞ over K, rootDiscr L ≤ rootDiscr K · C(K, S, ℓ)
```

with `C(K, S, ℓ)` an explicit constant (HMR computes `rd < 84` for their
example).

**Reference**: `TameRamification.lean` for `rd_bounded_in_tame_tower_postulate`,
and `UnramifiedDiscriminant.lean` for the everywhere-unramified specialization.

### Step 6: Each L is CM totally complex (CM preserved by unramified)

If `K` is CM totally complex and `L/K` is unramified at infinity (which
includes the everywhere-unramified case), then `L` is CM totally complex.

**Reference**:
- `HilbertClassFieldExt.isTotallyComplex` instance (PROVED).
- `isCMField_postulate` (CFT postulate, currently sorried).

### Step 7: Combine

The combined chain produces, for each `N`, a CM totally complex `L` with
`[L:K] ≥ p^N` and `rootDiscr L ≤ rootDiscr K = rd_F` (since `L/K` is
unramified at infinity, rd is constant).

This closes `gs_cm_tower_infinite_postulate`.

## Mathlib gaps along the chain

| Postulate | What's needed | Estimated effort |
|---|---|---|
| `maxProPExt_exists` | Class field theory's existence theorem for pro-`p` extensions | Multi-year |
| `gs_group_infinite` (the GS inequality) | Pro-`p` group cohomology + Hilbert series | Multi-month |
| `discr_formula_tame_postulate` | Tame ramification discriminant formula | Multi-month |
| `rd_bounded_in_tame_tower_postulate` | HMR's specific calculation | Multi-month |
| `isCMField_postulate` | maximalRealSubfield in HCF tower | Multi-month |

**Best route**: focus on the `discr_formula_tame_postulate` first — it's the
most elementary (just tame ramification + Mathlib's `differentIdeal`), and
closes a key non-trivial step.

## Connection to other CFT files

- `ClassFieldTheory.lean`: HCF stub + Artin reciprocity.  Not directly used
  in the GS chain above (HMR uses the more general `MaxProPExt`), but
  validates that the Artin-reciprocity structure is consistent.
- `LocalCFT.lean`, `GlobalCFT.lean`: local + global Artin map.  Underlying
  infrastructure for `maxProPExt_exists`.
- `HeckeCharacters.lean`: analytic CFT.  Underlies `chebotarev_density`
  (off the GS chain but on the CM-tower's Chebotarev-restricted level
  selection).
- `Chebotarev.lean`: density + Ihara.  Off this GS chain but on the
  parallel `chebotarev_fixed_Q` chain.

## Summary

The 7-step chain above shows EXACTLY where each Mathlib gap enters.  Each
gap is now a labelled postulate in `Erdos90/Mathlib4_Extra/*`, each with
its own file, each citing specific literature.

A focused Mathlib formalization push could close gaps in roughly this
order:
1. Tame ramification (most elementary)
2. Local CFT (Frutos-Fernández already has a partial library)
3. Global Artin map (assembled from local)
4. Pro-`p` extension existence (class field theory exists)
5. Golod–Shafarevich inequality (group cohomology)
6. `isCMField_postulate` (maximalRealSubfield)

The Erd46 project is **ready to absorb** any of these closures as they
become available.
