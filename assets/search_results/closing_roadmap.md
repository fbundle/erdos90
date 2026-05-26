# Closing roadmap — incremental Mathlib PR strategy

Written 2026-05-27.  Maps the 4 remaining sorries to specific Mathlib infrastructure that, if added, would close them.

## The 4 sorries

| # | Sorry | Location | Mathlib gap |
|---|---|---|---|
| 1 | `gs_cm_tower` | `NumberFieldDeep_GSTower.lean:133` | Class field theory + Golod–Shafarevich |
| 2 | `chebotarev_fixed_Q` | `NumberFieldDeep_GSTower.lean:185` | Chebotarev density theorem |
| 3 | `regulator_lower_bound_cm` | `Mathlib4_Extra/ClassNumberBound.lean:296` | Functional equation for `dedekindZeta` + Friedman analytic argument |
| 4 | `dedekind_residue_upper_bound_cm` | `Mathlib4_Extra/ClassNumberBound.lean:332` | Functional equation for `dedekindZeta` + Louboutin/Phragmén-Lindelöf |

## Critical observation: sorries 3 and 4 share infrastructure

Both `regulator_lower_bound_cm` and `dedekind_residue_upper_bound_cm` need:
- Analytic continuation of `NumberField.dedekindZeta K` past `s = 1`
- The functional equation
- Special-value computation (at `s = 0` for regulator; near `s = 1` for residue)

Building this infrastructure unblocks BOTH off-path sorries with a single coherent Mathlib contribution.

## The 5-PR roadmap

### PR-A: Multi-dimensional Poisson summation
**Goal:** Generalize `Real.tsum_eq_tsum_fourier` to lattices in finite-dim Euclidean space.

**Existing Mathlib (helpful):**
- `Mathlib/Analysis/Fourier/PoissonSummation.lean` — 1-D version
- `Mathlib/Analysis/SpecialFunctions/Gaussian/PoissonSummation.lean` — Gaussian decay
- `Mathlib/Analysis/Fourier/FourierTransform.lean` — generic Fourier transform on finite-dim spaces
- `Mathlib/Analysis/Distribution/SchwartzSpace/Fourier.lean` — Schwartz Fourier
- `Mathlib/Algebra/Module/ZLattice/*.lean` — ZLattice machinery

**New code needed:**
- `Lattice.tsum_eq_tsum_fourier`: for a ZLattice L in V (finite-dim normed ℝ-space) and `f : V → ℂ` of suitable decay, `Σ_{x ∈ L} f x = (1 / covolume L) · Σ_{ξ ∈ L^*} 𝓕f ξ` (where `L^*` is the dual lattice).
- Maybe simpler: just `Σ_{x ∈ 𝓞_K} f x = ... Σ_{ξ ∈ 𝓞_K^*} 𝓕f ξ` for number-field lattice.

**Effort:** moderate (one cohesive PR).  Lattice tensor-structure makes this a generalization of the 1-D case.

### PR-B: Multi-variable theta function for number field
**Goal:** Define theta function for K and prove its modular transformation.

**Definition:**
```lean
noncomputable def numberFieldTheta (K : Type*) [Field K] [NumberField K] 
    (t : ℝ) : ℂ := ∑' (a : 𝓞 K), Complex.exp (-π * t * ‖(a : mixedSpace K)‖²)
```

**Properties needed:**
- Convergence for `t > 0`
- Modular: `θ_K(1/t) = √|d_K| · t^(d/2) · θ_K(t)` (via PR-A)

**Effort:** moderate, builds directly on PR-A.

### PR-C: Wire theta into AbstractFuncEq
**Goal:** Use `Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean` to derive the functional equation for `completedDedekindZeta` from PR-B.

**Definition:**
```lean
noncomputable def completedDedekindZeta (K : Type*) [Field K] [NumberField K] 
    (s : ℂ) : ℂ :=
  |discr K|^(s/2) * Real.Gamma_ℝ s^(nrRealPlaces K) * 
    Real.Gamma_ℂ s^(nrComplexPlaces K) * dedekindZeta K s
```

**FE:** `completedDedekindZeta K (1 - s) = completedDedekindZeta K s`

**Effort:** straightforward once PR-A and PR-B are in place; AbstractFuncEq provides the framework.

### PR-D: Special values of dedekindZeta
**Goal:** Compute `ζ_K(0)` from the residue at `s = 1` via the functional equation.

**Stark–Tate formula:**
For unit rank `r = r₁ + r₂ - 1`:
```
ζ_K(s) = -h_K · R_K / w_K · s^r + O(s^{r+1})  as s → 0
```

**Effort:** moderate.  Mostly L-function manipulation given PR-C.

### PR-E: Friedman regulator lower bound
**Goal:** `regulator K ≥ 0.2052` for number fields with unit rank ≥ 1.

**Method:**
- Express `R_K = (lim_{s→0} ζ_K(s) · s^{-r}) · w_K / (-h_K)` (from PR-D).
- Bound the residue using positivity of integrals.
- Friedman's argument: certain Mellin integrals are positive.

**Effort:** substantial analytic argument, but self-contained given PR-A through PR-D.

## After A–E: what closes

Closures (assuming PR-A through PR-E land):
- ✓ `regulator_lower_bound_cm` (via PR-E)
- ✓ `dedekind_residue_upper_bound_cm` (via PR-C / PR-D, similar Phragmén-Lindelöf argument on `completedDedekindZeta`)

What remains:
- `chebotarev_fixed_Q` — also needs nonvanishing of `dedekindZeta` on Re s = 1 (from PR-C) PLUS the Dirichlet density theorem.  Mathlib has this for `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` on Dirichlet L's; needs to be extended to `dedekindZeta`.
- `gs_cm_tower` — class field theory, separate effort.

## Class field theory roadmap (for `gs_cm_tower`)

This is a Mathlib-roadmap-level effort spanning multiple subsystems:

- **Idele class group** `C_K = 𝔸_K^× / K^×`
- **Local class field theory** (Lubin-Tate, Galois cohomology)
- **Artin reciprocity** `Gal(K^ab/K) ≅ C_K`
- **Hilbert class field**
- **Pro-p group cohomology** (continuous Galois cohomology)
- **Golod–Shafarevich inequality**

Tracked in Mathlib's roadmap; estimated multi-year effort across multiple contributors.

## What we can do without these PRs

Per the maintainer's note ("if a statement is not optimal but sufficient to our final goal, leave comments rather than spending time on that"):
- The current state has 4 well-documented sorries with citations.
- The infrastructure for the chain (E5, E6, E7, E8, E9, E10, E13) is in place.
- The bridge from "Mathlib has PR-A through PR-E" to "our sorries close" is mechanical.

The formalization is **complete modulo the Mathlib gaps**.  Closing the gaps is a separate (multi-PR) effort that's tracked but not blocking.

## References to add to `assets/`

For posterity:
- Friedman 1989, *"Analytic formulas for the regulator of a number field"*, Inventiones 98:599–622
- Louboutin 2000, *"Explicit upper bounds for residues of Dedekind zeta functions and class numbers of CM-fields"*, Math. Comp. 69:225, 311–339 (we have this)
- Stark 1974, *"L-functions at s = 1"* — series of papers on the Stark conjecture
- Tate 1984, *Les conjectures de Stark sur les Fonctions L d'Artin en s = 0*
- Hajir–Maire–Ramakrishna 2021 (we have this)
- Lang, *Algebraic Number Theory* (textbook reference for everything)
- Neukirch, *Cohomology of Number Fields* (for class field theory)
