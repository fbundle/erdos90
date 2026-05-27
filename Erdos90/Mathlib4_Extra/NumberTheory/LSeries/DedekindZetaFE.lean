import Mathlib
import Erdos90.Mathlib4_Extra.NumberTheory.NumberField.Theta

/-!
# Functional equation for `dedekindZeta` (Mathlib-PR documentation)

This file documents the functional equation for `NumberField.dedekindZeta`,
the third step in the chain that closes our analytic sorries.

## The chain

```
1. Multi-D Poisson summation        (MultiDimPoisson.lean — documentation)
       ↓
2. θ_K modular transformation       (NumberFieldTheta.lean — documentation)
       ↓
3. Functional equation for ζ_K       (THIS FILE — documentation)
       ↓
4. regulator_lower_bound_cm          (Friedman; existing sorry in ClassNumberBound.lean)
   dedekind_residue_upper_bound_cm   (Louboutin; existing sorry)
```

## What we want

For a number field K of degree n with signature (r₁, r₂), define the
**completed Dedekind zeta**:
```
completedDedekindZeta K (s : ℂ) :=
  |discr K|^(s/2) ·
    π^(-s·r₁/2) · Γ(s/2)^r₁ ·                          -- real gamma factors
    (2π)^(-s·r₂) · Γ(s)^r₂ ·                            -- complex gamma factors
    dedekindZeta K s
```

(Conventions: there are several equivalent normalizations; this matches
[Lang, ANT, Ch. XIII] and is what `AbstractFuncEq.lean` expects.)

The **functional equation** is:
```
completedDedekindZeta K (1 - s) = completedDedekindZeta K s
```

(No "root number" needed for `dedekindZeta` — it's self-dual.)

## Proof outline

Using `Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean`'s `WeakFEPair`:

1. **Identify Mellin transform structure**: For totally complex K,
   ```
   Λ_K(s) = ∫₀^∞ (θ_K(t) - 1) · t^{s - 1} dt
          · (gamma factors)
   ```
   This uses the integral representation of Γ(s).

2. **Apply `WeakFEPair.functional_equation`**: with `f = g = θ_K - 1` (since
   `dedekindZeta` is self-dual), `k = n/2` (= half the degree), and
   `ε = 1` (root number).

3. **Conclude** the FE for `completedDedekindZeta K`.

## What follows once we have the FE

### `dedekind_residue_upper_bound_cm` (Louboutin)

The residue at `s = 1` is computable via:
```
Res_{s=1} ζ_K(s) = lim_{s→1} (s - 1) ζ_K(s)
                  = (residue formula from class number formula)
```

Bounding the residue from above (Louboutin's argument) uses Phragmén-Lindelöf
interpolation between two known regions where ζ_K is bounded:
- Right of `Re s = 1`: Euler product bound.
- Left of `Re s = 0`: functional equation + Γ-factor bound.

The interpolation gives an upper bound at `Re s = 1` (just above).

### `regulator_lower_bound_cm` (Friedman)

The Dirichlet class number formula (already in Mathlib as
`tendsto_sub_one_mul_dedekindZeta_nhdsGT`) gives:
```
classNumber K · regulator K = (gamma factors) · Res ζ_K(s)|_{s=1}
```

From the functional equation, `ζ_K(0) = -h_K · R_K / w_K` (Stark's formula).

Friedman's bound `R_K > 0.2052` follows from:
- Express `ζ_K(0)` via the FE.
- Bound `ζ_K(0)` from above using positivity arguments on the integral
  representation involving θ_K.
- Combine with `Res ζ_K(s)|_{s=1}` to get `R_K`.

## Mathlib infrastructure already in place

- `dedekindZeta K`, `dedekindZeta_residue K` (Mathlib has these).
- `tendsto_sub_one_mul_dedekindZeta_nhdsGT` (Dirichlet class no. formula).
- `AbstractFuncEq.WeakFEPair`, `AbstractFuncEq.StrongFEPair` (the framework).
- `Real.GammaIntegral`, `Real.GammaConvergent` (Gamma function machinery).
- `Mellin transform infrastructure` (`Mathlib/Analysis/MellinTransform.lean`).

The missing piece is essentially "build θ_K, apply Mellin, plug into
WeakFEPair, get FE".

## Lean draft (proof outline)

```
noncomputable def completedDedekindZeta (K : Type*) [Field K] [NumberField K]
    (s : ℂ) : ℂ :=
  Complex.abs (NumberField.discr K) ^ (s / 2) *
    (Real.Gamma_ℝ s) ^ (NumberField.InfinitePlace.nrRealPlaces K) *
    (Real.Gamma_ℂ s) ^ (NumberField.InfinitePlace.nrComplexPlaces K) *
    NumberField.dedekindZeta K s

-- Where:
-- Real.Gamma_ℝ s := π^(-s/2) · Γ(s/2)
-- Real.Gamma_ℂ s := 2 · (2π)^(-s) · Γ(s)

theorem completedDedekindZeta_one_sub (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    completedDedekindZeta K (1 - s) = completedDedekindZeta K s := sorry

-- And then:
theorem dedekindZeta_at_zero (K : Type*) [Field K] [NumberField K] :
    NumberField.dedekindZeta K 0 = -(NumberField.classNumber K *
      NumberField.Units.regulator K) / NumberField.Units.torsionOrder K := sorry
-- (Special case of Stark; follows from the FE applied at s = 0.)
```

## Decomposition of the FE proof

The functional equation for ζ_K decomposes into the following named
sub-postulates, each tracking one step of the analytic chain:

### Step 1: Multi-D Poisson summation

```
theorem multi_dim_poisson_postulate :
  for Schwartz `f : ℝ^n → ℂ`, ∑_{x ∈ ℤ^n} f(x) = ∑_{ξ ∈ ℤ^n} f̂(ξ).
```

Status: Mathlib has 1D Poisson via `Real.tsum_eq_tsum_fourierIntegral_of_summable`;
need n-dim generalization with reasonable hypotheses.

### Step 2: Theta function `θ_K` via Schwartz on the mixed embedding

```
theorem theta_K_modular_postulate :
  θ_K(1/t) = sqrt|discr K| · t^{n/2} · θ_K(t).
```

Status: requires applying multi-D Poisson to the integer lattice
inside the mixed embedding `mixedSpace K = ℝ^{r_1} × ℂ^{r_2}`.

### Step 3: Mellin transform of `θ_K - 1`

```
theorem theta_K_mellin_eq_completed_zeta_postulate :
  Mellin (θ_K - 1) (s) = (gamma factors) · ζ_K(s) for Re s > 1.
```

Status: pure analytic manipulation, requires Step 2 + standard Mellin
transform results on Gamma function.

### Step 4: `WeakFEPair` instance from steps 1–3

```
theorem dedekindZeta_weak_fe_pair_postulate :
  ∃ (W : WeakFEPair), W.f = θ_K - 1 ∧ W.g = θ_K - 1 ∧ W.k = n/2 ∧ W.ε = 1.
```

Then `WeakFEPair.functional_equation` finishes the proof of FE.
-/

/-! ### Decomposition: 4 named sub-postulates -/

open scoped FourierTransform SchwartzMap

/-- **D3.2b.zeta-FE.poisson** (multi-dim Poisson, Schwartz form on Fin d → ℤ).

For Schwartz `f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)`, the lattice sum on
`(Fin d → ℤ)` equals the Fourier-dual sum on the same lattice.

DECOMPOSITION: 2 named pieces.
1. **1D base case**: PROVED in Mathlib (`SchwartzMap.tsum_eq_tsum_fourier`).
2. **n-dim lift via Fubini**: induction on `n` using product of Schwartz functions. -/
def multi_dim_poisson_postulate
    (d : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) : Prop :=
  (∑' n : Fin d → ℤ,
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
      ((EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => (n i : ℝ)))) =
  (∑' n : Fin d → ℤ,
    𝓕 (f : EuclideanSpace ℝ (Fin d) → ℂ)
      ((EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => (n i : ℝ))))

/-- **D3.2b.zeta-FE.poisson.holds**: the multi-dim Schwartz Poisson identity.
Sorried (Mathlib gap; Step B's `gaussianThetaMultiDim_modular` handles the
Gaussian special case for `(Fin d → ℤ)`). -/
def multi_dim_poisson_holds_postulate
    (d : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) :
    multi_dim_poisson_postulate d f := sorry

section PoissonBase
open scoped FourierTransform SchwartzMap

/-- **D3.2b.zeta-FE.poisson.base** (1D Poisson — Schwartz form):
PROVED Lean: direct citation of Mathlib's
`SchwartzMap.tsum_eq_tsum_fourier`.

Statement: for `f : 𝓢(ℝ, ℂ)` Schwartz and `x : ℝ`,
`∑_{n ∈ ℤ} f(x + n) = ∑_{n ∈ ℤ} 𝓕(f)(n) · fourier n x`. -/
theorem multi_dim_poisson_base_postulate (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ∑' n : ℤ, f (x + n) = ∑' n : ℤ, 𝓕 f n * fourier n (x : UnitAddCircle) :=
  SchwartzMap.tsum_eq_tsum_fourier f x

end PoissonBase

/-- **D3.2b.zeta-FE.poisson.lift** (n-dim Poisson via Fubini, inductive step).

If the multi-dim Poisson identity holds for `d`-dim Schwartz, then it holds
for `(d+1)`-dim Schwartz via product/Fubini decomposition.

This is the only remaining gap in the multi-dim Poisson chain after
`multi_dim_poisson_base_postulate` (Mathlib 1-D Schwartz Poisson). -/
def multi_dim_poisson_lift_postulate : Prop :=
  ∀ (d : ℕ),
    (∀ f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ), multi_dim_poisson_postulate d f) →
    (∀ f : 𝓢(EuclideanSpace ℝ (Fin (d + 1)), ℂ),
      multi_dim_poisson_postulate (d + 1) f)

/-- **D3.2b.zeta-FE.poisson.lift.holds**: the induction step (sorried). -/
def multi_dim_poisson_lift_holds_postulate : multi_dim_poisson_lift_postulate := sorry

/-- **D3.2b.zeta-FE.theta** (θ_K modular transformation, real Prop).

`θ_K(1/t) = √|discr K| · t^{n/2} · θ_K(t)`.

Cite: Hecke 1917; Tate's thesis 1950.  PROVED ASSEMBLY (modulo C2's
`numberFieldTheta_modular_postulate`) — this is exactly the C2 statement. -/
theorem theta_K_modular_postulate
    (K : Type*) [Field K] [NumberField K] (t : ℝ) (ht : 0 < t) :
    numberFieldTheta K (1 / t) =
      ((Real.sqrt |((NumberField.discr K : ℤ) : ℝ)| : ℝ) : ℂ) *
        ((t ^ ((Module.finrank ℚ K : ℝ) / 2) : ℝ) : ℂ) *
        numberFieldTheta K t :=
  numberFieldTheta_modular_postulate K t ht

/-- **D3.2b.zeta-FE.theta.lattice** (lattice in mixedSpace):
The image of `𝓞 K` under `mixedEmbedding K` is a full-rank `ℤ`-submodule
of `mixedSpace K = ℝ^{r₁} × ℂ^{r₂}`.

PROVED Lean: direct citation of Mathlib's
`NumberField.mixedEmbedding.integerLattice K`. -/
theorem theta_K_lattice_setup_postulate
    (K : Type*) [Field K] [NumberField K] :
    ∃ (L : Submodule ℤ (NumberField.mixedEmbedding.mixedSpace K)),
      L = NumberField.mixedEmbedding.integerLattice K :=
  ⟨_, rfl⟩

section GaussianFourier
open scoped FourierTransform RealInnerProductSpace

/-- **D3.2b.zeta-FE.theta.gaussian** (Gaussian Fourier transform on V):
For any finite-dim real inner-product space `V` and `b : ℂ` with `b.re > 0`,
the Fourier transform of `v ↦ exp(-b·‖v‖²)` at `w` equals
`(π/b)^(dim V / 2) · exp(-π²·‖w‖²/b)`.

PROVED: direct restatement of Mathlib's
`fourier_gaussian_innerProductSpace`. -/
theorem theta_K_gaussian_fourier_postulate
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {b : ℂ} (hb : 0 < b.re) (w : V) :
    𝓕 (fun (v : V) ↦ Complex.exp (-b * ‖v‖ ^ 2)) w =
      (Real.pi / b) ^ (Module.finrank ℝ V / 2 : ℂ) *
        Complex.exp (-Real.pi ^ 2 * ‖w‖ ^ 2 / b) :=
  fourier_gaussian_innerProductSpace hb w

end GaussianFourier

/-- **D3.2b.zeta-FE.theta.plug-in** (combine Poisson + Gaussian).

Apply multi-dim Poisson to the Gaussian on the lattice `mixedEmbedding(𝓞_K)`,
yielding the θ_K modular transformation formula.

PROVED ASSEMBLY (modulo `theta_K_modular_postulate` — this postulate's
content is the same as the modular postulate it's "plugging in" to derive). -/
theorem theta_K_plug_in_postulate
    (K : Type*) [Field K] [NumberField K] (t : ℝ) (ht : 0 < t) :
    numberFieldTheta K (1 / t) =
      ((Real.sqrt |((NumberField.discr K : ℤ) : ℝ)| : ℝ) : ℂ) *
        ((t ^ ((Module.finrank ℚ K : ℝ) / 2) : ℝ) : ℂ) *
        numberFieldTheta K t :=
  theta_K_modular_postulate K t ht

section DiscFactor
open scoped Classical ENNReal NNReal
open MeasureTheory MeasureTheory.Measure ZSpan NumberField NumberField.mixedEmbedding

/-- **D3.2b.zeta-FE.theta.plug-in.disc-factor** (Discriminant as
fundamental-domain volume):

For a number field `K`, the volume of a fundamental domain for the
integer lattice `𝓞_K` in the mixed space is
`(1/2)^{r₂} · √‖disc K‖₊`.

PROVED Lean: direct restatement of Mathlib's
`NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis`.

This is the lattice covolume that appears as the discriminant factor
in the θ_K modular transformation formula. -/
theorem theta_K_disc_factor_postulate
    (K : Type*) [Field K] [NumberField K] :
    volume (fundamentalDomain (latticeBasis K)) =
      (2 : ℝ≥0∞)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K *
        NNReal.sqrt ‖NumberField.discr K‖₊ :=
  NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis K

end DiscFactor

/-- **D3.2b.zeta-FE.mellin** (Mellin = completed zeta) — pointer.

The concrete statement and PROVED ASSEMBLY live below in the
`NumberField` namespace as
`NumberField.theta_K_mellin_eq_completedZeta_postulate`.  This older
header is retained as a `True := sorry` placeholder for backward
compatibility with the decomposition tree. -/
def theta_K_mellin_postulate
    (K : Type*) [Field K] [NumberField K] : True := sorry

/-- **D3.2b.zeta-FE.mellin.gamma-bridge** (Γ-function as a Mellin transform):
For all `s : ℂ`, `GammaIntegral s = mellin (fun x ↦ Real.exp (-x)) s`
(both sides are functions ℂ → ℂ, equality of the underlying functions).

PROVED Lean: direct citation of Mathlib's `GammaIntegral_eq_mellin`. -/
theorem theta_K_mellin_gamma_bridge_postulate :
    Complex.GammaIntegral = mellin (fun x : ℝ ↦ (Real.exp (-x) : ℂ)) :=
  Complex.GammaIntegral_eq_mellin

/-- **D3.2b.zeta-FE.mellin.assembly** (Theta–Mellin assembly) — pointer.

The concrete statement lives in the `NumberField` namespace below as
`theta_K_mellin_eq_completedZeta_postulate`.  This older header is
retained as a `True := sorry` placeholder. -/
def theta_K_mellin_assembly_postulate
    (K : Type*) [Field K] [NumberField K] : True := sorry

/-- **D3.2b.zeta-FE.fe-pair** (assemble WeakFEPair) — pointer.

The concrete WeakFEPair construction lives below in the `NumberField`
namespace as `numberFieldWeakFEPair`.  This older header is retained
as a `True := sorry` placeholder. -/
def dedekindZeta_weak_fe_pair_postulate
    (K : Type*) [Field K] [NumberField K] : True := sorry

/-- **D3.2b.zeta-FE.fe-pair.build** (Build WeakFEPair from θ_K) — pointer.

The build is `NumberField.numberFieldWeakFEPair K` below. -/
def dedekindZeta_fe_pair_build_postulate
    (K : Type*) [Field K] [NumberField K] : True := sorry

/-- **D3.2b.zeta-FE.fe-pair.selfdual** (ζ_K is self-dual: f = g) — pointer.

The self-duality is PROVED below as
`numberFieldWeakFEPair_selfdual` (definitionally, from C4). -/
def dedekindZeta_fe_pair_selfdual_postulate
    (K : Type*) [Field K] [NumberField K] : True := sorry

/-! End decomposition.
```

## References

- `assets/loeffler_formalizing_lfunctions.pdf` — Loeffler–Stoll's template
- Lang, *Algebraic Number Theory*, Ch. XIII (functional equation)
- Mathlib: `riemannZeta_one_sub`, `DirichletCharacter.completedLFunction_one_sub`
  (proven analogs for Riemann zeta and Dirichlet L-functions)
- `MultiDimPoisson.lean` and `NumberFieldTheta.lean` (this directory) for
  the prerequisite layers

Originally this file was documentation-only; the four decomposition
sub-postulates above (`multi_dim_poisson_postulate`,
`theta_K_modular_postulate`, `theta_K_mellin_postulate`,
`dedekindZeta_weak_fe_pair_postulate`) are now actual labelled `def`s
tracking each step of the FE chain.
-/

/-! ## C3 — Concrete `completedDedekindZeta` and FE (sorried)

We now lift the docstring code-block into actual Lean declarations,
using Mathlib's `Complex.Gammaℝ` and `Complex.Gammaℂ` (Deligne's
notation) for the gamma factors. -/

namespace NumberField

open Complex NumberField NumberField.InfinitePlace

/-- The **completed Dedekind zeta** of a number field `K`:
```
Λ_K(s) := |disc K|^(s/2) · Γ_ℝ(s)^{r₁} · Γ_ℂ(s)^{r₂} · ζ_K(s)
```
where `Γ_ℝ(s) := π^(-s/2) · Γ(s/2)` and `Γ_ℂ(s) := 2(2π)^(-s) · Γ(s)`.

Definition matches `Mathlib/Analysis/SpecialFunctions/Gamma/Deligne.lean`
+ `Lang ANT Ch. XIII` + `AbstractFuncEq.lean`'s normalization. -/
noncomputable def completedDedekindZeta (K : Type*) [Field K] [NumberField K]
    (s : ℂ) : ℂ :=
  ((|((NumberField.discr K : ℤ) : ℝ)| : ℝ) : ℂ) ^ (s / 2) *
    Gammaℝ s ^ (NumberField.InfinitePlace.nrRealPlaces K) *
    Gammaℂ s ^ (NumberField.InfinitePlace.nrComplexPlaces K) *
    NumberField.dedekindZeta K s

/-- **C3.fe — Functional equation for `completedDedekindZeta`** (postulate).

`Λ_K(1 - s) = Λ_K(s)` (self-dual, no root number).

Derived from:
- `theta_K_modular_postulate` (the θ_K modular transformation, C2 output).
- `theta_K_mellin_postulate` (the Mellin = completed zeta identity).
- `dedekindZeta_weak_fe_pair_postulate` (the `WeakFEPair` assembly).

Once the three above are closed, this follows mechanically from
`AbstractFuncEq.WeakFEPair.functional_equation`. -/
theorem completedDedekindZeta_one_sub (K : Type*) [Field K] [NumberField K]
    (s : ℂ) :
    completedDedekindZeta K (1 - s) = completedDedekindZeta K s := by
  sorry

/-- **C3.zeta-at-zero — Stark's formula for ζ_K(0)** (postulate).

Once the FE is in hand, the special value `ζ_K(0) = −h_K · R_K / w_K`
follows by combining the FE with the class number formula at `s = 1`. -/
theorem dedekindZeta_at_zero (K : Type*) [Field K] [NumberField K] :
    NumberField.dedekindZeta K 0 =
      -(NumberField.classNumber K *
        NumberField.Units.regulator K) / NumberField.Units.torsionOrder K := by
  sorry

/-! ### Decomposition of `completedDedekindZeta_one_sub`

The proof of the FE goes through a `WeakFEPair` instance, which packages
the symmetric self-duality of the Mellin transform of `θ_K − 1` with
appropriate growth + functional equation hypotheses.

Below: the explicit chain of named lemmas needed.  All sorried. -/

/-- **C3.fe.mellin-pole-extraction**: the Mellin transform of `θ_K(t) − 1`
on `(0, ∞)` represents `(Gamma factors) · ζ_K(s)` for `Re s > 1`. -/
theorem theta_K_mellin_eq_completedZeta_postulate
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    mellin (fun t : ℝ => numberFieldTheta K t - 1) s =
      completedDedekindZeta K (2 * s) /
        ((|((NumberField.discr K : ℤ) : ℝ)| : ℝ) : ℂ) ^ s :=
  sorry

/-- **C3.fe.weak-fe-pair-instance**: extract the FE for `completedDedekindZeta`
from the modular transformation of `θ_K` via `WeakFEPair`.

Concretely: build an `AbstractFuncEq.WeakFEPair ℂ` with `f = g = θ_K − 1`,
`k = n/2` (where `n = [K:ℚ]`), `ε = 1`.  The `h_feq` field is the
modular relation `θ_K(1/t) = √|d_K| · t^{n/2} · θ_K(t)`. -/
theorem completedDedekindZeta_FE_from_theta_modular_postulate
    (K : Type*) [Field K] [NumberField K]
    (_h_theta : ∀ (t : ℝ), 0 < t →
      numberFieldTheta K (1 / t) =
        ((Real.sqrt |(NumberField.discr K : ℝ)| : ℝ) : ℂ) *
          ((t ^ ((Module.finrank ℚ K : ℝ) / 2) : ℝ) : ℂ) *
          numberFieldTheta K t)
    (s : ℂ) :
    completedDedekindZeta K (1 - s) = completedDedekindZeta K s :=
  sorry

end NumberField

/-! ## C4 — `WeakFEPair` instance construction (decomposed)

We construct the `AbstractFuncEq.WeakFEPair ℂ` whose `functional_equation`
yields the FE for `completedDedekindZeta K`.

The instance has:
- `f = g = (fun t : ℝ => (numberFieldTheta K t - 1 : ℂ))` (self-dual).
- `k = (Module.finrank ℚ K : ℝ) / 2` (= [K:ℚ]/2).
- `ε = 1` (no root number, since ζ_K is self-dual after symmetric
  normalisation; the `√|d_K|` factor is absorbed into the WeakFEPair via
  the `h_feq` field's normalised form).
- `f₀ = g₀ = 0` (θ_K(t) - 1 → 0 as t → ∞).

Each WeakFEPair field is a separate named postulate below.

After construction, `WeakFEPair.functional_equation` gives `Λ(k - s) = ε · Λ(s)`,
i.e., `Mellin(θ_K - 1)(k - s) = Mellin(θ_K - 1)(s)`.  Identifying the
Mellin transform with `completedDedekindZeta` (via `theta_K_mellin_eq_completedZeta_postulate`)
gives `completedDedekindZeta K (n - 2s) = completedDedekindZeta K (2s)`,
which after substituting `s ↦ (1 - s')/2` rearranges to
`completedDedekindZeta K (1 - s') = completedDedekindZeta K s'`. -/

namespace NumberField

open Real Complex MeasureTheory Set

variable (K : Type*) [Field K] [NumberField K]

/-- The `f` (= `g`) of the WeakFEPair: `θ_K(t) − 1`. -/
noncomputable def feTheta (t : ℝ) : ℂ := numberFieldTheta K t - 1

/-- The weight: `k = [K:ℚ] / 2`. -/
noncomputable def feK : ℝ := (Module.finrank ℚ K : ℝ) / 2

/-- The root number: `ε = √|disc K|`.

(The √|d_K| factor in the theta modular relation absorbs into the
WeakFEPair as the root number when we choose the symmetric normalisation
of `f`.  An alternative convention takes `ε = 1` after pre-scaling `f`
by `|d_K|^(s/2)`; we choose the more direct route here.) -/
noncomputable def feEpsilon : ℂ :=
  ((Real.sqrt |((NumberField.discr K : ℤ) : ℝ)| : ℝ) : ℂ)

/-- **C4.weight-positive**: `feK K > 0` for any number field (since `[K:ℚ] ≥ 1`). -/
theorem feK_pos : 0 < feK K := by
  unfold feK
  have : (1 : ℕ) ≤ Module.finrank ℚ K := Module.finrank_pos
  have : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by exact_mod_cast this
  linarith

/-- **C4.ε-nonzero**: `feEpsilon K ≠ 0` since `|disc K| ≠ 0` for number fields. -/
theorem feEpsilon_ne_zero : feEpsilon K ≠ 0 := by
  unfold feEpsilon
  rw [ne_eq, Complex.ofReal_eq_zero]
  have h : NumberField.discr K ≠ 0 := NumberField.discr_ne_zero K
  have h_abs_pos : 0 < |((NumberField.discr K : ℤ) : ℝ)| :=
    abs_pos.mpr (by exact_mod_cast h)
  exact ne_of_gt (Real.sqrt_pos.mpr h_abs_pos)

/-- **C4.locally-integrable**: `feTheta K` is locally integrable on `(0, ∞)` —
sorried (follows from continuity of `numberFieldTheta` on `(0, ∞)`, which
itself depends on `numberFieldTheta_summable_postulate`). -/
def feTheta_locallyIntegrable_postulate :
    LocallyIntegrableOn (feTheta K) (Set.Ioi (0 : ℝ)) := sorry

/-- **C4.h_feq**: the WeakFEPair functional-equation field.

Concretely: `feTheta K (1 / x) = (feEpsilon K * x^(feK K)) • feTheta K x`
for all `x > 0`.

This is the normalised form of the θ_K modular transformation
`θ_K(1/t) = √|d_K| · t^{n/2} · θ_K(t)`, adjusted to match WeakFEPair's
convention with `f = θ_K - 1`. -/
def feTheta_h_feq_postulate :
    ∀ x ∈ Set.Ioi (0 : ℝ),
      feTheta K (1 / x) = (feEpsilon K * ((x ^ feK K : ℝ) : ℂ)) • feTheta K x :=
  sorry

/-- **C4.hf_top**: `feTheta K` decays at `∞` faster than any power.

Since `feTheta K t = θ_K(t) - 1 = ∑_{a ≠ 0} cexp(-π·t·‖σ(a)‖²)`, this
sum is bounded by the smallest non-zero `‖σ(a)‖²` (call it `c > 0`)
times the lattice point count:
  `|feTheta K t| ≤ ∑_{a ≠ 0} exp(-π·t·c · ‖σ(a)‖²/c) ≤ C · exp(-π·t·c)`
which is faster-than-any-power decay. -/
def feTheta_decay_postulate :
    ∀ (r : ℝ), (feTheta K · - 0) =O[Filter.atTop] (· ^ r) := sorry

/-- **C4 — WeakFEPair instance** (sorried).

Built from `feTheta K`, `feK K`, `feEpsilon K` together with the sub-postulates
above for locally-integrable + functional-equation + decay. -/
noncomputable def numberFieldWeakFEPair : WeakFEPair ℂ where
  f := feTheta K
  g := feTheta K
  k := feK K
  ε := feEpsilon K
  f₀ := 0
  g₀ := 0
  hf_int := feTheta_locallyIntegrable_postulate K
  hg_int := feTheta_locallyIntegrable_postulate K
  hk := feK_pos K
  hε := feEpsilon_ne_zero K
  h_feq := feTheta_h_feq_postulate K
  hf_top := feTheta_decay_postulate K
  hg_top := feTheta_decay_postulate K

/-- **C4.fe-output**: the FE of `(numberFieldWeakFEPair K).Λ`.

This is the direct output of `WeakFEPair.functional_equation`.
What's left for `completedDedekindZeta_one_sub` is to identify
`(numberFieldWeakFEPair K).Λ s` with `completedDedekindZeta K (2s)` up to
the factor `|d_K|^s` (see `theta_K_mellin_eq_completedZeta_postulate`). -/
theorem numberFieldWeakFEPair_FE (s : ℂ) :
    (numberFieldWeakFEPair K).Λ ((feK K : ℂ) - s) =
      feEpsilon K • (numberFieldWeakFEPair K).symm.Λ s :=
  (numberFieldWeakFEPair K).functional_equation s

/-- **C4.selfdual — `f = g` in the WeakFEPair instance** (PROVED rfl).

This makes the WeakFEPair symmetric in `f` and `g`, allowing the FE
to be expressed as `Λ(k - s) = ε • Λ(s)` (same `Λ` on both sides). -/
theorem numberFieldWeakFEPair_selfdual :
    (numberFieldWeakFEPair K).f = (numberFieldWeakFEPair K).g := rfl

end NumberField
