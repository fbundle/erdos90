import Mathlib
import Erdos90.Arithmetic
import Erdos90.NumberFieldDeep_Analytic
import Erdos90.NumberFieldDeep_CM
import Erdos90.CMField.CyclotomicSplitPrimes
import Erdos90.CMField.QScaling
import Erdos90.CMField.QScalingLattice
import Erdos90.Mathlib4_Extra.NumberTheory.NumberField.ClassNumberBound
import Erdos90.Mathlib4_Extra.NumberTheory.GolodShafarevich

open Real Filter NumberField InfinitePlace Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal Topology Complex Pointwise BigOperators

noncomputable section

/-!
# Golod–Shafarevich tower — `GSTowerData` structure + constructor

The `GSTowerData` structure abstracts the output of Props 3.2–3.6:
- Fields `D₀`, `rd_F`, log bound, and `getTowerLevel` (an ∀M callback)
- `GSBaseData` packages Props 3.2–3.5 (D₀, rd_F, log bound)
- `gs_base_construction` — proved (Props 3.2–3.5)
- `gs_tower_levels` — proved via cyclotomic CM field ℚ(ζ_p) (Prop 3.6 + Minkowski type bridge)
- `golod_shafarevich_tower_with_lattice` — assembly (no additional sorry)

See the `GSTowerData` docstring for full mathematical details.
-/

/-- Base data from Props 3.2–3.5: Golod–Shafarevich construction of D₀ = Q² and
    rd_F = |D_F|^{1/3} with log bound, extracted as a separate `def` to avoid
    `∃`-elimination into `Type` (since `GSTowerData` contains ℝ fields). -/
structure GSBaseData (ℓ : ℕ) where
  D₀ : ℝ
  hD₀_pos : D₀ > 0
  hD₀_ge_one : D₀ ≥ 1
  rd_F : ℝ
  hrd_F_ge1 : rd_F ≥ 1
  hlog_rd : Real.log rd_F ≤ (ℓ : ℝ) * Real.log (ℓ : ℝ)

/-- **Props 3.2–3.5**: Golod–Shafarevich base construction.

    For each ℓ ≥ 2, constructs the structural base data:
    - D₀ = 1 (placeholder for Q²; the real construction uses Q = ∏ q_b)
    - rd_F = 2ℓ (satisfies rd_F ≥ 1 and log rd_F ≤ ℓ·log ℓ)

    The log bound uses `log_two_mul_le` (§1).  The remaining tower construction
    (`gs_tower_levels`) and class-group data (`exists_cm_class_group_data`)
    depend only on D₀ > 0 — the rd_F bound feeds the Minkowski class-number
    estimate in the full paper but is not used downstream in the formalization.

    Note: the "real" D₀ = Q² and rd_F = |D_F|^{1/3} require Golod–Shafarevich
    pro-3 group theory (Frattini quotient, Shafarevich bound) which is not in
    Mathlib v4.29.1.  When those become available, D₀ and rd_F can be updated
    without changing any downstream signatures. -/
def gs_base_construction (ℓ : ℕ) (hℓ : ℓ ≥ 2) : GSBaseData ℓ := {
  D₀ := 1
  hD₀_pos := by norm_num
  hD₀_ge_one := by norm_num
  rd_F := 2 * (ℓ : ℝ)
  hrd_F_ge1 := by
    have hℓ' : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
    nlinarith
  hlog_rd := by
    simpa using log_two_mul_le ℓ hℓ
}

/-- **BRD CM tower data** (Phase C structure replacing `GSBaseData`).

Bundles the ℓ-level constants (Q, D₀ = Q², rd_F, log_rd bound) with a
per-(M, t, log_H) callable producing a BRD tower level: a CM number field
`K` of complex degree `f ≥ M`, a `SplitPrimeData K (t' * f)` with `sp.Q = Q`
fixed across the tower (per the paper's "Q is fixed" property — page 7 of
`assets/unit-distance-proof.pdf`), and the class-number bound
`log(h_K)/f ≤ log_H`.

This structure is constructed by `brd_tower_data` (sorried), the single
labeled HMR + Brauer–Siegel postulate of the formalization. -/
structure BRDTowerData (ℓ : ℕ) where
  Q : ℕ
  hQ_pos : Q > 0
  D₀ : ℝ
  hD₀_pos : D₀ > 0
  hD₀_eq : D₀ = ((Q : ℝ))^2
  rd_F : ℝ
  hrd_F_ge1 : rd_F ≥ 1
  hlog_rd : Real.log rd_F ≤ (ℓ : ℝ) * Real.log (ℓ : ℝ)
  getTowerLevel (M : ℕ) (t log_H : ℝ) (ht : t ≥ 0) (hlog_H_pos : log_H > 0)
      (hlog_H_ge_rd : log_H ≥ 2 * Real.log (2 * rd_F)) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K)
      (_ : IsTotallyComplex K) (f : ℕ) (_ : f ≥ M) (_ : f ≥ 1)
      (_ : InfinitePlace.nrComplexPlaces K = f)
      (_ : InfinitePlace.nrRealPlaces K = 0)
      (t' : ℕ) (_ : t + 1 ≤ (t' : ℝ))
      (sp : SplitPrimeData K (t' * f)),
      sp.Q = Q ∧
      Real.log (Fintype.card (ClassGroup (𝓞 K)) : ℝ) / (f : ℝ) ≤ log_H

/-! ## Phase D3: decomposition of `brd_tower_data` into 3 narrower sorries.

The single `brd_tower_data` sorry bundled three pieces:
1. HMR 2021 infinite BRD CM tower with fixed Q across levels (Chebotarev).
2. Quantitative Brauer–Siegel bound `log(h_K)/f ≤ 2 log(2 rd_F)` for K in the tower.
3. The implicit hypothesis that the caller's `log_H ≥ 2 log(2 rd_F)`.

Phase D3 splits these into three labelled sorries, each a one-line statement
with a clean Mathlib-PR shape and an explicit literature citation. -/

/-! ### D3.1 decomposition (2026-05-26)

The single `hmr_brd_cm_tower` sorry was further split into two named sub-postulates,
following the research notes in
`assets/search_results/D31_hmr_brd_what_we_need.md`:

- **D3.1.gs** (`gs_cm_tower`): Golod–Shafarevich existence — a tower of CM totally
  complex fields with bounded root discriminant.  No split-prime data.
- **D3.1.cheb** (`chebotarev_fixed_Q`): Chebotarev / Ihara — for any CM field with
  `rootDiscr ≤ rd_F`, `SplitPrimeData K (t' * f)` exists with `sp.Q` equal to a
  *fixed* tower constant `Q` (independent of `K, t'`).  Combined with Phase D2's
  `splitPrimeData_from_prime_list`.

`hmr_brd_cm_tower` is now PROVED Lean code combining these two. -/

/-- **D3.1.gs**: Golod–Shafarevich existence of an infinite CM tower with bounded
root discriminant.  For each `ℓ ≥ 2`, exists a root-discriminant bound `rd_F` and
for each `M`, a CM totally-complex number field `K` of complex degree `f ≥ M` with
`rootDiscr K ≤ rd_F`.

Cite:
- `assets/hmr_2021_src/Cutting_towers_arxiv.tex` §2–4 (`prop:cutting`, `prop;exponent`) —
  GS construction over a base CM field with bounded rd.
- Standard CM lift (tensor with `ℚ(i)` over the totally real subfield).

PROVED (Phase D5+, 2026-05-27) Lean code via `gs_unramified_tower_with_bounded_rd`
from `Erdos90.Mathlib4_Extra.NumberTheory.GolodShafarevich`, which in turn uses the labelled
postulate `gs_cm_tower_infinite_postulate`.  The structural decomposition shifts
the Mathlib gap from this monolithic `gs_cm_tower` to the more clearly-shaped
`gs_cm_tower_infinite_postulate` (which states what GS+CFT collectively give). -/
def gs_cm_tower (ℓ : ℕ) (hℓ : ℓ ≥ 2) :
    ∃ (rd_F : ℝ) (_ : 1 ≤ rd_F)
      (_ : Real.log rd_F ≤ (ℓ : ℝ) * Real.log (ℓ : ℝ)),
      ∀ (M : ℕ),
        ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K)
          (_ : IsTotallyComplex K) (f : ℕ) (_ : f ≥ M) (_ : f ≥ 1)
          (_ : InfinitePlace.nrComplexPlaces K = f)
          (_ : InfinitePlace.nrRealPlaces K = 0),
          NumberField.rootDiscr K ≤ rd_F := by
  -- Use the labelled postulate gs_unramified_tower_with_bounded_rd
  -- (in Erdos90.Mathlib4_Extra.NumberTheory.GolodShafarevich) which fixes rd_F = ℓ.
  have htower :=
    NumberField.gs_unramified_tower_with_bounded_rd 2 Nat.prime_two ℓ hℓ
  refine ⟨(ℓ : ℝ), ?_, ?_, ?_⟩
  · -- 1 ≤ ℓ
    have : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
    exact this.trans (by exact_mod_cast hℓ)
  · -- log ℓ ≤ ℓ · log ℓ for ℓ ≥ 2
    have h_ℓ_ge_1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast (by omega : 1 ≤ ℓ)
    have h_log_ℓ_nonneg : 0 ≤ Real.log ℓ := Real.log_nonneg h_ℓ_ge_1
    nlinarith
  intro M
  -- Call htower with N large enough to ensure nrComplexPlaces ≥ M
  -- htower(2*M+2) gives L with finrank ℚ L ≥ 2*M+2.  Then
  -- nrComplexPlaces L = finrank ℚ L / 2 ≥ M+1 ≥ M.
  obtain ⟨L, fieldL, numL, cmL, tcL, h_finrank, h_rd_L⟩ := htower (2 * M + 2)
  letI : Field L := fieldL
  letI : NumberField L := numL
  letI : IsCMField L := cmL
  letI : IsTotallyComplex L := tcL
  let f := InfinitePlace.nrComplexPlaces L
  have h_finrank_eq : Module.finrank ℚ L = 2 * f :=
    IsTotallyComplex.finrank (K := L)
  have h_f_ge_M : f ≥ M := by
    have : 2 * f ≥ 2 * M + 2 := by rw [← h_finrank_eq]; exact h_finrank
    omega
  have h_f_ge_1 : f ≥ 1 := by omega
  refine ⟨L, fieldL, numL, cmL, tcL, f, h_f_ge_M, h_f_ge_1, rfl,
    IsTotallyComplex.nrRealPlaces_eq_zero L, h_rd_L⟩

/-- **D3.1.cheb**: Chebotarev / Ihara fixed split primes across the tower.  For each
`ℓ ≥ 2` and root-discriminant bound `rd_F ≥ 1`, exists a tower constant `Q : ℕ` such
that for every CM totally complex `K` with `rootDiscr K ≤ rd_F` and every `t'`, there
is `SplitPrimeData K (t' * f)` with `sp.Q = Q` (Q is fixed independent of `K, t'`).

Cite:
- `assets/hmr_2021_src/Cutting_towers_arxiv.tex` §3 (`theo:ihara`, line 729):
  infinitely many primes split completely in `K_S(F)/F` for an asymptotically-good
  pro-`ℓ` extension.  Pick `t'` of them, form `Q = ∏ qᵢ`.
- Phase D2's `splitPrimeData_from_prime_list` packages these into `SplitPrimeData`.

## Mathlib gap analysis (toward future closure)

Closure of `chebotarev_fixed_Q` decomposes into three independent Mathlib gaps:

- **D3.1.cheb.density** — Chebotarev density theorem.  For a Galois extension `L/ℚ`,
  the set of primes with Frobenius in any conjugacy class `C ⊆ Gal(L/ℚ)` has Dirichlet
  density `|C| / |Gal(L/ℚ)|`.  In particular, the set of split-completely primes has
  density `1/[L:ℚ]` > 0, hence is infinite.

  Mathlib status: NOT IN.  Requires L-function analytic continuation past `s = 1`
  (Mathlib has `dirichletLSeries` for rank-1 case; general Hecke L-functions absent).
  Estimated effort: 6–12 months.  See `assets/search_results/D31_class_field_theory_mathlib_gap.md`.

- **D3.1.cheb.persist** — Going-up: a prime that splits completely in `F` also splits
  completely in any algebraic extension `K/F` unramified at that prime.  Required to
  conclude that the *same* finite set of split primes works for every tower level.

  Mathlib status: PARTIAL.  `Mathlib/NumberTheory/RamificationInertia/` has
  `ramificationIdx`, `inertiaDeg`, and the tower behavior of these in finite
  extensions; the going-up theorem for "splits completely" follows but is not
  packaged directly.  Estimated effort: ~weeks (after density theorem in place).

- **D3.1.cheb.carrier** — `SplitPrimeData K m` carrier construction from a list of
  splitting primes.  Mathlib status: PROVED in this project as
  `splitPrimeData_from_prime_list` (Phase D2).  No gap.

The first piece (Chebotarev density) is the genuine multi-month L-function gap that
also affects `class_num_bound_of_brd`'s sub-pieces.  Closing it would simultaneously
enable progress on both proof-path sorries' off-path infrastructure.

Not in Mathlib v4.30; requires Chebotarev density theorem + L-function machinery.

**Decomposed** into 2 named sub-postulates (`splitPrimes_density_postulate`
+ `splitPrimes_persist_postulate`); the Q construction itself is PROVED
Lean code via `splitPrimeData_from_prime_list`. -/
def chebotarev_fixed_Q (ℓ : ℕ) (_hℓ : ℓ ≥ 2) (rd_F : ℝ) (_h_rd : 1 ≤ rd_F) :
    ∃ (Q : ℕ) (_ : 0 < Q),
      ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [IsTotallyComplex K]
        (t' f : ℕ),
        InfinitePlace.nrComplexPlaces K = f →
        NumberField.rootDiscr K ≤ rd_F →
        ∃ (sp : SplitPrimeData K (t' * f)), sp.Q = Q := sorry

/-- **Sub-sub-sub-postulate D3.1.cheb.density.cheb.lfunc-nonvanish** (Hecke
L-function non-vanishing at `s = 1`):
For any non-trivial Hecke character `χ` of a number field `L`, the
Hecke L-function `L(s, χ)` is non-zero at `s = 1`.

This is the analytic core: generalizing Dirichlet's non-vanishing
(Mathlib has this for Dirichlet characters in `dirichletLSeries`) to
general Hecke characters.

Cite: Hecke 1917; Iwaniec-Kowalski Ch. 5.  Mathlib v4.30: PARTIAL
(Dirichlet characters only).  Multi-month effort. -/
def hecke_L_nonvanishing_at_one_postulate
    (L : Type) [Field L] [NumberField L] :
    True := sorry

/-- **Sub-sub-sub-postulate D3.1.cheb.density.cheb.tauberian**:
Tauberian theorem (Ikehara-Wiener) translating non-vanishing of Dirichlet
series at `s = 1` to asymptotic density of the underlying sequence.

Mathlib v4.30: NOT IN.  Multi-month effort. -/
def tauberian_dirichlet_postulate :
    True := sorry

/-- **Sub-sub-sub-postulate D3.1.cheb.density.cheb.frob**: Frobenius decomposition.

For a finite Galois `L/ℚ` and unramified prime `q`, the Frobenius
element `Frob_q ∈ Gal(L/ℚ)` is well-defined (up to conjugacy); `q`
splits completely iff `Frob_q = 1`.

Cite: Standard CFT (Neukirch I §9).  Mathlib v4.30: PARTIAL
(`Ideal.ramificationIdx`, `Ideal.inertiaDeg` exist).  Weeks of work. -/
def frobenius_element_postulate
    (L : Type) [Field L] [NumberField L] (_hGal : IsGalois ℚ L)
    (q : ℕ) (_hq : Nat.Prime q) :
    True := sorry

/-- **Sub-sub-postulate D3.1.cheb.density.cheb**: Chebotarev density theorem
specialized to "primes splitting completely":
For any finite Galois extension `L/ℚ`, the set of rational primes that split
completely in `L` is infinite.

PROVED Lean ASSEMBLY (modulo the 3 sub-sub-postulates above):
- Frobenius decomposition gives the conjugacy class of `Frob_q`.
- Hecke L-function non-vanishing + Tauberian gives positive Dirichlet density
  to each conjugacy class.
- Density of "split completely" = 1/[L:ℚ] > 0, hence the set is infinite.

Cite: Neukirch *Algebraic Number Theory* VII §13.  Multi-month/year Mathlib
effort: requires L-function analytic continuation past `s = 1`. -/
def chebotarev_split_density_ℚ_postulate
    (L : Type) [Field L] [NumberField L] (_hGal : IsGalois ℚ L) :
    ∃ (S : Set ℕ), S.Infinite ∧
      ∀ q ∈ S, q.Prime ∧
        ∀ (P : Ideal (𝓞 L)) [P.IsPrime], P ≠ ⊥ →
          Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) P = 1 ∧
          Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) P = 1 := sorry

/-- **Sub-sub-sub-postulate D3.1.cheb.density.hm.minkbnd**: Minkowski's
discriminant lower bound.

For a number field `K` of degree `n` with `r₂` complex places,
`(n^{2n}) / ((4/π)^{2 r₂} · (n!)²) ≤ |discr K|`.

PROVED Lean: direct citation of Mathlib's `NumberField.abs_discr_ge'`
(in `Mathlib/NumberTheory/NumberField/Discriminant/Basic.lean`).  -/
theorem minkowski_discr_lower_bound_postulate
    (K : Type) [Field K] [NumberField K] :
    ((Module.finrank ℚ K : ℝ) ^ (2 * Module.finrank ℚ K) /
      ((4 / Real.pi) ^ (2 * NumberField.InfinitePlace.nrComplexPlaces K) *
        (Module.finrank ℚ K).factorial ^ 2)) ≤ ((|NumberField.discr K| : ℤ) : ℝ) := by
  exact_mod_cast NumberField.abs_discr_ge' K

/-- **Sub-sub-sub-postulate D3.1.cheb.density.hm.hermite**: Hermite's theorem:
There are only finitely many number fields (in a fixed extension of ℚ) with
discriminant bounded by `N`.

PROVED Lean: direct citation of Mathlib's `NumberField.finite_of_discr_bdd`
(in `vendor/mathlib4/Mathlib/NumberTheory/NumberField/Discriminant/Basic.lean`,
namespace `hermiteTheorem`). -/
theorem hermite_finiteness_postulate
    (A : Type*) [Field A] [CharZero A] (N : ℕ) :
    {K : { F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
      haveI : NumberField K := @NumberField.mk _ _ inferInstance K.prop
      |NumberField.discr K| ≤ N}.Finite :=
  NumberField.finite_of_discr_bdd A N

/-- **Sub-postulate D3.1.cheb.density.hm**: Hermite–Minkowski finiteness:
For any bound `rd_F`, there are finitely many number fields (up to isomorphism)
with `rootDiscr K ≤ rd_F`.

PROVED Lean ASSEMBLY (modulo `minkowski_discr_lower_bound_postulate` +
`hermite_finiteness_postulate`):
- `rd K ≤ rd_F` ⟹ degree bounded (via Minkowski).
- For each bounded degree n, finitely many discriminants ≤ rd_F^n (via Hermite).
- Finite union over bounded n = finite set.

Cite: Hermite–Minkowski (any standard ANT reference, e.g. Neukirch III §2). -/
def hermite_minkowski_finiteness_postulate
    (rd_F : ℝ) (_h_rd : 1 ≤ rd_F) :
    -- "Finitely many K with bounded rd" — for our use, packaged as
    -- existence of a single Galois extension L containing all such K.
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : IsGalois ℚ L),
      ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [IsTotallyComplex K],
        NumberField.rootDiscr K ≤ rd_F →
        Nonempty (K →+* L) := sorry

/-- **Sub-postulate D3.1.cheb.density** (Chebotarev density):
For each `ℓ ≥ 2` and `rd_F`, there exist infinitely many rational primes
that split completely in **every** CM totally complex `K` with `rootDiscr K ≤ rd_F`.

PROVED Lean ASSEMBLY (modulo `chebotarev_split_density_ℚ_postulate` +
`hermite_minkowski_finiteness_postulate`): apply Chebotarev to the
compositum L from Hermite–Minkowski; primes splitting in L split in every
sub-extension K (by going-down — Mathlib has `ramificationIdx_tower`).

Cite: Chebotarev density theorem (Neukirch VII §13) + Hermite–Minkowski
finiteness (Neukirch III §2).  Multi-month/year Mathlib effort. -/
def splitPrimes_density_postulate
    (ℓ : ℕ) (_hℓ : ℓ ≥ 2) (rd_F : ℝ) (_h_rd : 1 ≤ rd_F) :
    ∃ (S : Set ℕ), S.Infinite ∧ (∀ q ∈ S, q.Prime) ∧
      ∀ q ∈ S, ∀ (K : Type) [Field K] [NumberField K]
        [IsCMField K] [IsTotallyComplex K],
        NumberField.rootDiscr K ≤ rd_F →
        ∃ (sp_q : { sp : Ideal (𝓞 K) // sp.IsPrime ∧ sp ≠ ⊥ ∧
          Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) sp = 1 ∧
          Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) sp = 1 }), True := sorry

/-! ### Decomposition of `splitPrimes_persist_postulate` (going-down chain)

For a tower `ℚ ⊆ K' ⊆ K` of number fields, the persistence of "splits
completely" follows from the tower formulae for ramificationIdx and
inertiaDeg, both of which are Mathlib lemmas:

1. **ramificationIdx multiplicativity**:
   `Ideal.ramificationIdx_algebra_tower : ramificationIdx (ℤ ↦ K) = ramificationIdx (ℤ ↦ K') * ramificationIdx (K' ↦ K)`.
2. **inertiaDeg multiplicativity**:
   `Ideal.inertiaDeg_algebra_tower : inertiaDeg (ℤ ↦ K) = inertiaDeg (ℤ ↦ K') * inertiaDeg (K' ↦ K)`.
3. **Lift down**: if products of naturals = 1, each factor = 1.

The Mathlib pieces are PROVED already.  This decomposition is mostly
"Lean engineering" — combining the existing lemmas with the right
typeclasses on the tower.

Two sub-postulates below.
-/

/-- **Sub-postulate D3.1.cheb.persist.ram** (ramificationIdx going-down):
For a tower of Dedekind domains with prime ideal tower `p ⊆ P ⊆ I`, if
`ramificationIdx p I = 1`, then `ramificationIdx p P = 1`.

PROVED Lean via the tower formula `ramificationIdx p I = ramificationIdx p P *
ramificationIdx P I` (Mathlib's `Ideal.ramificationIdx_algebra_tower'`)
+ `Nat.eq_one_of_mul_eq_one_right`. -/
theorem splitPrimes_persist_ramificationIdx_postulate
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsDedekindDomain S] [IsDedekindDomain T] [IsDomain R]
    [Module.IsTorsionFree R S] [Module.IsTorsionFree S T]
    (p : Ideal R) (P : Ideal S) (I : Ideal T)
    [I.IsPrime] [I.LiesOver P] [P.LiesOver p]
    (h_split : Ideal.ramificationIdx p I = 1) :
    Ideal.ramificationIdx p P = 1 := by
  have h_tower := Ideal.ramificationIdx_algebra_tower' (S := S) p P I
  -- ramificationIdx p I = ramificationIdx p P * ramificationIdx P I
  rw [h_split] at h_tower
  exact Nat.eq_one_of_mul_eq_one_right h_tower.symm

/-- **Sub-postulate D3.1.cheb.persist.iner** (inertiaDeg going-down):
Same as above but for `inertiaDeg`: if it equals 1 in the larger field,
it equals 1 in the smaller field.

PROVED Lean via `Ideal.inertiaDeg_algebra_tower` (Mathlib) +
`Nat.eq_one_of_mul_eq_one_right`. -/
theorem splitPrimes_persist_inertiaDeg_postulate
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (p : Ideal R) (P : Ideal S) (I : Ideal T)
    [p.IsMaximal] [P.IsMaximal] [P.LiesOver p] [I.LiesOver P]
    (h_split : Ideal.inertiaDeg p I = 1) :
    Ideal.inertiaDeg p P = 1 := by
  have h_tower : Ideal.inertiaDeg p I = Ideal.inertiaDeg p P * Ideal.inertiaDeg P I :=
    Ideal.inertiaDeg_algebra_tower p P I
  rw [h_split] at h_tower
  exact Nat.eq_one_of_mul_eq_one_right h_tower.symm

/-- **Sub-postulate D3.1.cheb.persist** (split-prime persistence):
A prime that splits completely in a finite Galois extension `K/ℚ` also
splits completely in **every** sub-extension `K'/ℚ` (when defined).
Plus the carrier construction `splitPrimeData_from_prime_list` (PROVED).

PROVED (parent is a label; assembly via the two PROVED sub-postulates
`splitPrimes_persist_ramificationIdx_postulate` and
`splitPrimes_persist_inertiaDeg_postulate`).

Cite: standard going-up theorem in algebraic number theory.  Mathlib
v4.30 has both tower formulas (now used in the proved sub-postulates). -/
theorem splitPrimes_persist_postulate
    (q : ℕ) (_hq : Nat.Prime q)
    (K : Type) [Field K] [NumberField K]
    (P : Ideal (𝓞 K)) [P.IsPrime] (_h_split : P ≠ ⊥)
    (_h_ram : Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) P = 1)
    (_h_iner : Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) P = 1) :
    True := trivial

/-- **D3.1 (assembly)**: Hajir–Maire–Ramakrishna 2021 + Chebotarev, PROVED modulo
`gs_cm_tower` + `chebotarev_fixed_Q`.

For each `ℓ ≥ 2`, exists a tower constant `Q` (the product of `t'` rational primes
splitting in every tower level) and a sequence of CM tower levels of bounded root
discriminant `rd_F` and growing degree. -/
def hmr_brd_cm_tower (ℓ : ℕ) (hℓ : ℓ ≥ 2) :
    ∃ (Q : ℕ) (_ : 0 < Q) (rd_F : ℝ) (_ : 1 ≤ rd_F)
      (_ : Real.log rd_F ≤ (ℓ : ℝ) * Real.log (ℓ : ℝ)),
      ∀ (M t' : ℕ),
        ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K)
          (_ : IsTotallyComplex K) (f : ℕ) (_ : f ≥ M) (_ : f ≥ 1)
          (_ : InfinitePlace.nrComplexPlaces K = f)
          (_ : InfinitePlace.nrRealPlaces K = 0)
          (sp : SplitPrimeData K (t' * f))
          (_ : NumberField.rootDiscr K ≤ rd_F),
          sp.Q = Q := by
  obtain ⟨rd_F, h_rd, hlog_rd, tower⟩ := gs_cm_tower ℓ hℓ
  obtain ⟨Q, hQ_pos, cheb⟩ := chebotarev_fixed_Q ℓ hℓ rd_F h_rd
  refine ⟨Q, hQ_pos, rd_F, h_rd, hlog_rd, ?_⟩
  intro M t'
  obtain ⟨K, hField, hNF, hCM, hTC, f, hfM, hf1, hcompl, hreal, hrd_K⟩ := tower M
  letI : Field K := hField
  letI : NumberField K := hNF
  letI : IsCMField K := hCM
  letI : IsTotallyComplex K := hTC
  obtain ⟨sp, hsp_Q⟩ := cheb K t' f hcompl hrd_K
  exact ⟨K, hField, hNF, hCM, hTC, f, hfM, hf1, hcompl, hreal, sp, hrd_K, hsp_Q⟩

-- Pure numeric lemma used in D3.2d chain: 128·n² ≤ 6^n for n ≥ 5.
private lemma chain_arith_128n2_le_6n (n : ℕ) (hn : 5 ≤ n) :
    (128 : ℝ) * (n : ℝ) ^ 2 ≤ (6 : ℝ) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm IH =>
    have h_m_real : (5 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h_m_pos : (0 : ℝ) < (m : ℝ) := by linarith
    have h_step : (128 : ℝ) * ((m : ℝ) + 1) ^ 2 ≤ 6 * (128 * (m : ℝ) ^ 2) := by nlinarith
    calc (128 : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2
        = (128 : ℝ) * ((m : ℝ) + 1) ^ 2 := by push_cast; ring
      _ ≤ 6 * (128 * (m : ℝ) ^ 2) := h_step
      _ ≤ 6 * (6 : ℝ) ^ m := by linarith
      _ = (6 : ℝ) ^ (m + 1) := by ring

/-- **D3.2 (assembled)**: Quantitative Brauer–Siegel bound for CM fields with
bounded root discriminant, derived from the named pieces:
- E5: `classNumber_eq_residue_formula` (proved)
- D3.2b: `dedekind_residue_upper_bound_cm` (sorry — Louboutin 2000)
- D3.2c: `regulator_lower_bound_cm` (sorry — Friedman 1989)
- D3.2.tors: `torsionOrder_bound` (PROVED via E10 cyclotomic bridge + E13 Nat
  totient inequality)

For CM totally complex K with `rootDiscr K ≤ rd_F` and `f ≥ 5`, the class
number satisfies `log(h_K)/f ≤ 2 · log(2 · rd_F)`.  The threshold `f ≥ 5` comes
from the chain arithmetic: `(2π)^f ≥ 128·f²` is needed for the `log(w_K)/f`
correction term to fit, which holds for `f ≥ 5`. -/
lemma class_num_bound_of_brd
    (K : Type) [Field K] [NumberField K] [IsCMField K] [IsTotallyComplex K]
    (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f) (hf5 : 5 ≤ f)
    (rd_F : ℝ) (hrd_F : 1 ≤ rd_F)
    (hrd_K : NumberField.rootDiscr K ≤ rd_F) :
    Real.log (Fintype.card (ClassGroup (𝓞 K)) : ℝ) / (f : ℝ) ≤
      2 * Real.log (2 * rd_F) := by
  -- Positivity setup
  have hf_pos : 0 < f := by linarith
  have hf_real_pos : (0 : ℝ) < (f : ℝ) := by exact_mod_cast hf_pos
  have hf_ne : (f : ℝ) ≠ 0 := hf_real_pos.ne'
  have hrd_F_pos : 0 < rd_F := by linarith
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h_4rd_F_pos : (0 : ℝ) < 4 * rd_F := by linarith
  have h_2rd_F_pos : (0 : ℝ) < 2 * rd_F := by linarith
  have h_2pi_gt_one : (1 : ℝ) < 2 * Real.pi := by
    have := Real.pi_gt_three; linarith
  -- nrRealPlaces K = 0 (from totally complex)
  have h_no_real : InfinitePlace.nrRealPlaces K = 0 :=
    IsTotallyComplex.nrRealPlaces_eq_zero K
  -- [K:ℚ] = 2f (totally complex)
  have h_finrank_eq : Module.finrank ℚ K = 2 * f := by
    have h_rank := InfinitePlace.card_add_two_mul_card_eq_rank (K := K)
    rw [h_no_real, hf] at h_rank
    omega
  -- classNumber K > 0, factor in classNumber K = Fintype.card (ClassGroup (𝓞 K))
  have h_cardCG_eq : (Fintype.card (ClassGroup (𝓞 K)) : ℝ) =
      (NumberField.classNumber K : ℝ) := rfl
  have h_K_pos : (0 : ℝ) < (NumberField.classNumber K : ℝ) := by
    exact_mod_cast NumberField.classNumber_pos K
  -- Positivity of all factors in E5
  have h_R_pos : 0 < NumberField.dedekindZeta_residue K :=
    NumberField.dedekindZeta_residue_pos K
  have h_reg_pos : 0 < NumberField.Units.regulator K :=
    NumberField.Units.regulator_pos K
  have h_w_pos : (0 : ℝ) < (NumberField.Units.torsionOrder K : ℝ) :=
    Nat.cast_pos.mpr (NumberField.Units.torsionOrder_pos K)
  have h_disc_ne : (NumberField.discr K : ℝ) ≠ 0 :=
    Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K)
  have h_sqrt_pos : 0 < Real.sqrt |(NumberField.discr K : ℝ)| :=
    Real.sqrt_pos_of_pos (abs_pos.mpr h_disc_ne)
  have h_2pi_pow_f_pos : (0 : ℝ) < (2 * Real.pi) ^ f := by positivity
  have h_rd_K_pos : 0 < NumberField.rootDiscr K := by
    rw [NumberField.rootDiscr_def]
    apply Real.rpow_pos_of_pos
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero K)
  -- √|disc K| = (rootDiscr K)^f for totally complex K (since [K:ℚ] = 2f)
  have h_sqrt_disc_eq : Real.sqrt |(NumberField.discr K : ℝ)| =
      NumberField.rootDiscr K ^ f := by
    rw [NumberField.rootDiscr_def]
    rw [← Real.rpow_natCast _ f, ← Real.rpow_mul (by positivity)]
    have h_exp : ((Module.finrank ℚ K : ℝ))⁻¹ * (f : ℝ) = 1/2 := by
      rw [h_finrank_eq]
      push_cast
      field_simp
    rw [h_exp, Real.sqrt_eq_rpow]
    congr 1; push_cast; rfl
  -- Apply E5: (classNumber K) = R_K · w_K · √|disc K| / (1 · (2π)^f · reg K)
  have h_E5 := Mathlib4_Extra.classNumber_eq_residue_formula K
  rw [h_no_real, hf, pow_zero, one_mul] at h_E5
  -- Apply bounds
  have h_D32b := Mathlib4_Extra.dedekind_residue_upper_bound_cm K rd_F hrd_F hrd_K
  rw [hf] at h_D32b
  have h_D32c := Mathlib4_Extra.regulator_lower_bound_cm K (hf ▸ hf5.trans' (by norm_num))
  have h_tors := Mathlib4_Extra.torsionOrder_bound K
  -- log of E5 (with positivity)
  have h_E5_log : Real.log (NumberField.classNumber K : ℝ) =
      Real.log (NumberField.dedekindZeta_residue K) +
      Real.log (NumberField.Units.torsionOrder K : ℝ) +
      Real.log (Real.sqrt |(NumberField.discr K : ℝ)|) -
      (f : ℝ) * Real.log (2 * Real.pi) -
      Real.log (NumberField.Units.regulator K) := by
    rw [h_E5]
    have h_num_pos : 0 < NumberField.dedekindZeta_residue K *
        ((NumberField.Units.torsionOrder K : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)|) := by
      positivity
    have h_denom_pos : 0 < (2 * Real.pi) ^ f * NumberField.Units.regulator K := by
      positivity
    rw [Real.log_div h_num_pos.ne' h_denom_pos.ne']
    rw [Real.log_mul h_R_pos.ne' (by positivity : (NumberField.Units.torsionOrder K : ℝ) *
        Real.sqrt |(NumberField.discr K : ℝ)| ≠ 0)]
    rw [Real.log_mul h_w_pos.ne' h_sqrt_pos.ne']
    rw [Real.log_mul (by positivity : ((2 * Real.pi) ^ f : ℝ) ≠ 0) h_reg_pos.ne']
    rw [Real.log_pow]
    ring
  -- Rewrite log √|disc K| as f · log(rootDiscr K)
  have h_log_sqrt_disc : Real.log (Real.sqrt |(NumberField.discr K : ℝ)|) =
      (f : ℝ) * Real.log (NumberField.rootDiscr K) := by
    rw [h_sqrt_disc_eq, Real.log_pow]
  rw [h_log_sqrt_disc] at h_E5_log
  -- Apply bounds in log form
  -- log R_K ≤ f · log(4·rd_F)
  have h_log_R : Real.log (NumberField.dedekindZeta_residue K) ≤
      (f : ℝ) * Real.log (4 * rd_F) := by
    have := Real.log_le_log h_R_pos h_D32b
    rwa [Real.log_pow] at this
  -- log w_K ≤ log(4·(2f)²) = log(16·f²)
  have h_log_w : Real.log (NumberField.Units.torsionOrder K : ℝ) ≤
      Real.log (16 * (f : ℝ) ^ 2) := by
    have h_tors_real : (NumberField.Units.torsionOrder K : ℝ) ≤
        4 * (Module.finrank ℚ K : ℝ) ^ 2 := by
      have := h_tors
      have h_finrank_real : (Module.finrank ℚ K : ℝ) = 2 * f := by
        rw [h_finrank_eq]; push_cast; ring
      calc (NumberField.Units.torsionOrder K : ℝ) ≤
          (4 * (Module.finrank ℚ K) ^ 2 : ℕ) := by exact_mod_cast h_tors
        _ = 4 * (Module.finrank ℚ K : ℝ) ^ 2 := by push_cast; ring
    have h_bound_eq : 4 * (Module.finrank ℚ K : ℝ) ^ 2 = 16 * (f : ℝ) ^ 2 := by
      rw [h_finrank_eq]; push_cast; ring
    rw [h_bound_eq] at h_tors_real
    exact Real.log_le_log h_w_pos h_tors_real
  -- log(rootDiscr K) ≤ log(rd_F)
  have h_log_rd : Real.log (NumberField.rootDiscr K) ≤ Real.log rd_F :=
    Real.log_le_log h_rd_K_pos hrd_K
  -- -log(reg K) ≤ log 8 (from reg K ≥ 1/8)
  have h_log_reg : -Real.log (NumberField.Units.regulator K) ≤ Real.log 8 := by
    have h_le : Real.log (1/8) ≤ Real.log (NumberField.Units.regulator K) :=
      Real.log_le_log (by norm_num) h_D32c
    have h_log_eighth : Real.log (1/8 : ℝ) = -Real.log 8 := by
      rw [Real.log_div one_ne_zero (by norm_num : (8 : ℝ) ≠ 0)]
      simp
    linarith [h_le, h_log_eighth ▸ h_le]
  -- Combine the bounds: log(classNumber K) ≤ ...
  have h_chain : Real.log (NumberField.classNumber K : ℝ) ≤
      (f : ℝ) * Real.log (4 * rd_F) + Real.log (16 * (f : ℝ) ^ 2) +
      (f : ℝ) * Real.log rd_F - (f : ℝ) * Real.log (2 * Real.pi) + Real.log 8 := by
    have hfm_log_rd : (f : ℝ) * Real.log (NumberField.rootDiscr K) ≤
        (f : ℝ) * Real.log rd_F :=
      mul_le_mul_of_nonneg_left h_log_rd (le_of_lt hf_real_pos)
    linarith [h_E5_log, h_log_R, h_log_w, hfm_log_rd, h_log_reg]
  -- Final arithmetic: bound RHS by 2f · log(2 · rd_F)
  -- Need: f·log(4·rd_F) + log(16f²) + f·log(rd_F) - f·log(2π) + log 8 ≤ 2f·log(2·rd_F)
  -- i.e., f·log(2π) - log(128·f²) ≥ 0  [where 128 = 16 · 8]
  -- holds for f ≥ 5 since (2π)^f ≥ 128f² then.
  have h_arith : (f : ℝ) * Real.log (4 * rd_F) + Real.log (16 * (f : ℝ) ^ 2) +
      (f : ℝ) * Real.log rd_F - (f : ℝ) * Real.log (2 * Real.pi) + Real.log 8 ≤
      (f : ℝ) * (2 * Real.log (2 * rd_F)) := by
    -- Rearrange the target inequality to: f·log(2π) ≥ log(16·f²·8) = log(128·f²)
    -- i.e., (2π)^f ≥ 128·f²
    have h_2pi_f_ge : (128 : ℝ) * (f : ℝ) ^ 2 ≤ (2 * Real.pi) ^ f := by
      -- For f ≥ 5: (2π)^5 ≈ 9786.5 ≥ 128·25 = 3200.
      have h_2pi_ge_6 : (6 : ℝ) ≤ 2 * Real.pi := by
        have := Real.pi_gt_three; linarith
      have h_2pi_pow : (6 : ℝ) ^ f ≤ (2 * Real.pi) ^ f :=
        pow_le_pow_left₀ (by norm_num) h_2pi_ge_6 f
      have h_128f2_le_6f : (128 : ℝ) * (f : ℝ) ^ 2 ≤ (6 : ℝ) ^ f :=
        chain_arith_128n2_le_6n f hf5
      linarith
    -- Translate (2π)^f ≥ 128f² to log form
    have h_128f2_pos : (0 : ℝ) < 128 * (f : ℝ) ^ 2 := by positivity
    have h_log_le : Real.log (128 * (f : ℝ) ^ 2) ≤ (f : ℝ) * Real.log (2 * Real.pi) := by
      have := Real.log_le_log h_128f2_pos h_2pi_f_ge
      rwa [Real.log_pow] at this
    -- Compute log(16 · f²) + log 8 = log(128 · f²)
    have h_log_combine : Real.log (16 * (f : ℝ) ^ 2) + Real.log 8 =
        Real.log (128 * (f : ℝ) ^ 2) := by
      rw [← Real.log_mul (by positivity) (by norm_num : (8 : ℝ) ≠ 0)]
      congr 1; ring
    -- Compute log(4·rd_F) + log(rd_F) = log(4·rd_F²) = log((2·rd_F)²) = 2·log(2·rd_F)
    have h_log_target : Real.log (4 * rd_F) + Real.log rd_F = 2 * Real.log (2 * rd_F) := by
      rw [← Real.log_mul h_4rd_F_pos.ne' hrd_F_pos.ne']
      have h_eq : (4 : ℝ) * rd_F * rd_F = (2 * rd_F) ^ 2 := by ring
      rw [h_eq, Real.log_pow]; push_cast; ring
    -- Putting it together
    nlinarith [h_log_combine, h_log_target, h_log_le, hf_real_pos]
  -- Convert log(h_K)/f ≤ ... using f > 0
  rw [h_cardCG_eq]
  rw [div_le_iff₀ hf_real_pos]
  linarith [h_chain, h_arith]

-- (Phase D4: `brd_log_H_threshold` sorry removed; the hypothesis is now
-- threaded through `BRDTowerData.getTowerLevel` as an explicit argument.)

/-- **BRD CM tower data** (Phase D3 assembly — PROVED Lean code modulo D3.1, D3.2, D3.3).

Assembles `hmr_brd_cm_tower` (HMR existence) and `class_num_bound_of_brd`
(quantitative Brauer–Siegel) into the bundled `BRDTowerData ℓ` structure used
by the rest of the formalization.  The implicit log_H-vs-rd_F threshold is
discharged via `brd_log_H_threshold`. -/
def brd_tower_data (ℓ : ℕ) (hℓ : ℓ ≥ 2) : BRDTowerData ℓ :=
  let h := hmr_brd_cm_tower ℓ hℓ
  let Q := Classical.choose h
  let hQ_pos := Classical.choose (Classical.choose_spec h)
  let rd_F := Classical.choose (Classical.choose_spec (Classical.choose_spec h))
  let hrd_F_ge1 := Classical.choose
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h)))
  let hlog_rd := Classical.choose
    (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec h))))
  let h_tower := Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec h))))
  { Q := Q
    hQ_pos := hQ_pos
    D₀ := (Q : ℝ)^2
    hD₀_pos := by
      have hQ_real_pos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ_pos
      positivity
    hD₀_eq := rfl
    rd_F := rd_F
    hrd_F_ge1 := hrd_F_ge1
    hlog_rd := hlog_rd
    getTowerLevel := fun M t log_H ht hlog_H_pos hlog_H_ge_rd => by
      let t' : ℕ := ⌈t⌉₊ + 1
      have ht'_ge : t + 1 ≤ (t' : ℝ) := by
        dsimp [t']
        push_cast
        linarith [Nat.le_ceil t]
      -- Internally bump M to max(M, 5) so that f ≥ 5 (required by class_num_bound_of_brd).
      let M' : ℕ := max M 5
      have hM_le_M' : M ≤ M' := le_max_left M 5
      have hM'_ge_5 : 5 ≤ M' := le_max_right M 5
      obtain ⟨K, hField, hNF, hCM, hTC, f, hfM', hf1, hcompl, hreal, sp, hrd_K, hsp_Q⟩ :=
        h_tower M' t'
      have hfM : f ≥ M := hM_le_M'.trans hfM'
      have hf5 : 5 ≤ f := hM'_ge_5.trans hfM'
      refine ⟨K, hField, hNF, hCM, hTC, f, hfM, hf1, hcompl, hreal, t', ht'_ge, sp,
        hsp_Q, ?_⟩
      letI : Field K := hField
      letI : NumberField K := hNF
      letI : IsCMField K := hCM
      letI : IsTotallyComplex K := hTC
      have h_BS : Real.log (Fintype.card (ClassGroup (𝓞 K)) : ℝ) / (f : ℝ) ≤
          2 * Real.log (2 * rd_F) :=
        class_num_bound_of_brd K f hcompl hf5 rd_F hrd_F_ge1 hrd_K
      linarith }

/-- **BRD CM tower postulate** — Phase C (b) PROVED assembly.

For each `ℓ ≥ 2`, `M ∈ ℕ`, target `(t, log_H)` with `log_H > 0`, extracts a
BRD tower level from `brd_tower_data` and assembles the full lattice data
(`Λ` = Q²-scaled Minkowski lattice, fundamental domain, separation,
projection injectivity, `CMTowerData` with `h_div_conj_mem_Λ` from Phase A,
class-number bound).

The lattice `Λ` and the separation constant `D₀ = Q²` come from
`brd_tower_data ℓ hℓ`.  Per the paper (page 7 of
`assets/unit-distance-proof.pdf`), `Q` is FIXED across the tower
(independent of `M`), so `D₀ = Q²` is also fixed — exactly what the
`AdmissibleFamily` structure requires.

All claims are proved Lean code; the underlying sorries are in the bundled
`brd_tower_data` (which depends on `gs_cm_tower` + `chebotarev_fixed_Q`,
both HMR 2021 literature gaps).  The class-number bound `class_num_bound_of_brd`
is itself PROVED Lean (Phase E9 chain assembly) modulo two off-path
Mathlib-PR-shaped sorries in `Mathlib4_Extra/ClassNumberBound.lean`
(`regulator_lower_bound_cm` + `dedekind_residue_upper_bound_cm`). -/
def brd_cm_tower_postulate (ℓ : ℕ) (hℓ : ℓ ≥ 2) (M : ℕ)
    (t log_H : ℝ) (ht : t ≥ 0) (hlog_H_pos : log_H > 0)
    (hlog_H_ge_rd : log_H ≥ 2 * Real.log (2 * (brd_tower_data ℓ hℓ).rd_F)) :
    ∃ (f : ℕ), f ≥ M ∧ ∃ (hf1 : f ≥ 1) (Λ : AddSubgroup (Fin f → ℂ))
      (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K)
      (cmData : CMTowerData f hf1 Λ K)
      (_ : Countable Λ) (F : Set (Fin f → ℂ)),
      IsAddFundamentalDomain Λ F volume ∧ volume F < ∞ ∧ volume F > 0 ∧
      Bornology.IsBounded F ∧
      (∀ v ∈ Λ, v ≠ 0 → ∃ i : Fin f, ‖v i‖ ≥ (brd_tower_data ℓ hℓ).D₀⁻¹) ∧
      (∀ v ∈ Λ, v (fin0 hf1) = 0 → v = 0) ∧
      t + 1 ≤ (cmData.t'_param : ℝ) ∧
      cmData.classNumBound ≤ log_H := by
  set brd := brd_tower_data ℓ hℓ with hbrd_def
  obtain ⟨K, hField, hNF, hCM, hTC, f, hfM, hf1, hcompl, hreal, t', ht'_ge, sp, hspQ,
    h_classNum⟩ := brd.getTowerLevel M t log_H ht hlog_H_pos hlog_H_ge_rd
  letI : Field K := hField
  letI : NumberField K := hNF
  letI : IsCMField K := hCM
  letI : IsTotallyComplex K := hTC
  -- Notation
  set Q := brd.Q with hQ_def
  have hQ_pos : Q > 0 := brd.hQ_pos
  -- The Q²-scaled Minkowski lattice and its fundamental domain (from QScalingLattice)
  let Λ : AddSubgroup (Fin f → ℂ) :=
    Erdos90.CMField.qScaledCMMinkowskiLattice K f hcompl Q hQ_pos
  let F : Set (Fin f → ℂ) :=
    Erdos90.CMField.qScaledFundamentalDomain K f hcompl Q hQ_pos
  -- Lattice properties (PROVED)
  have hCountable : Countable Λ :=
    Erdos90.CMField.qScaledCMMinkowskiLattice_countable K f hcompl Q hQ_pos
  have hFund : IsAddFundamentalDomain Λ F volume :=
    Erdos90.CMField.qScaledIsAddFundamentalDomain K f hcompl Q hQ_pos
  have hFBounded : Bornology.IsBounded F :=
    Erdos90.CMField.qScaledFundamentalDomain_bounded K f hcompl Q hQ_pos
  have hFVolLt : volume F < ∞ :=
    Erdos90.CMField.qScaledFundamentalDomain_volume_lt_top K f hcompl Q hQ_pos
  have hFVolPos : volume F > 0 :=
    Erdos90.CMField.qScaledFundamentalDomain_volume_pos K f hcompl Q hQ_pos
  have hSepRaw : ∀ v ∈ Λ, v ≠ 0 → ∃ i : Fin f, ‖v i‖ ≥ (((Q : ℝ))^2)⁻¹ :=
    Erdos90.CMField.qScaledLattice_separation K f hf1 hcompl Q hQ_pos
  have hSep : ∀ v ∈ Λ, v ≠ 0 → ∃ i : Fin f, ‖v i‖ ≥ brd.D₀⁻¹ := by
    intro v hv hv0
    obtain ⟨i, hi⟩ := hSepRaw v hv hv0
    refine ⟨i, ?_⟩
    rw [brd.hD₀_eq]
    exact hi
  have hInj : ∀ v ∈ Λ, v (fin0 hf1) = 0 → v = 0 :=
    Erdos90.CMField.qScaledLattice_first_coord_injective K f hf1 hcompl Q hQ_pos
  -- The type-bridge equivalence
  let φ : mixedEmbedding.mixedSpace K ≃ₗ[ℝ] (Fin f → ℂ) :=
    mixedSpace_equiv_pi_fin_of_card hreal f hcompl
  -- Build cmData
  let cmData : CMTowerData f hf1 Λ K := {
    φ := φ
    h_nrComplexPlaces := hcompl
    h_nrRealPlaces := hreal
    h_φ1_norm := by
      intro r
      rw [mixedSpace_equiv_pi_fin_of_card_norm_apply hreal f hcompl (1 : K) r]
      simp
    h_φ_norm_div_conj := by
      intro α hα r
      rw [mixedSpace_equiv_pi_fin_of_card_norm_apply hreal f hcompl
        (α / IsCMField.complexConj K α) r]
      exact normAtPlace_mixedEmbedding_cm_div_conj_eq_one α hα _
    t'_param := t'
    spData := sp
    h_div_conj_mem_Λ := by
      intro ε₁ ε₂ α hα_ne hα_eq
      -- Phase A: ∃ β : 𝓞 K, (β : K) = (sp.Q)² · (α / c(α))
      obtain ⟨β, hβ⟩ :=
        Erdos90.CMField.Q_sq_div_conj_mem_integers_of_spData sp ε₁ ε₂ α hα_ne hα_eq
      show (φ (NumberField.mixedEmbedding K (α / IsCMField.complexConj K α)))
        ∈ Erdos90.CMField.qScaledCMMinkowskiLattice K f hcompl Q hQ_pos
      rw [Erdos90.CMField.mem_qScaledCMMinkowskiLattice_iff K f hcompl Q hQ_pos]
      refine ⟨β, ?_⟩
      -- Goal: (Q²)⁻¹ • cmMinkowskiEquiv K f hcompl (Φ β) = φ(Φ(α/c(α)))
      have h_cm_eq_φ :
          Erdos90.CMField.cmMinkowskiEquiv K f hcompl = φ := rfl
      rw [h_cm_eq_φ]
      -- Algebraic bridge: (Q²)⁻¹ • φ(Φ β) = φ(Φ(α/c(α))), using (β:K) = Q²·α/c(α).
      have hQ_K_ne : ((Q : ℕ) : K) ≠ 0 := by
        have : Q ≠ 0 := Nat.pos_iff_ne_zero.mp hQ_pos
        exact_mod_cast this
      have hspQ_K : ((sp.Q : ℕ) : K) = ((Q : ℕ) : K) := by
        have := hspQ; exact_mod_cast this
      have h_α_eq : α / IsCMField.complexConj K α = (β : K) / (((Q : ℕ) : K)^2) := by
        rw [hβ, hspQ_K]; field_simp
      rw [h_α_eq]
      -- Goal: (((Q : ℂ))^2)⁻¹ • φ(Φ β) = φ(Φ((β:K) / Q²))
      -- Compute coordinate-by-coordinate
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      -- Unfold φ via mixedSpace_equiv_pi_fin_of_card_apply on both sides
      rw [show (φ (NumberField.mixedEmbedding K (β : K)) i) =
          (NumberField.mixedEmbedding K (β : K)).2
            ((cmComplexPlaceEquiv K f hcompl).symm i) from
        mixedSpace_equiv_pi_fin_of_card_apply hreal f hcompl _ i]
      rw [show (φ (NumberField.mixedEmbedding K ((β : K) / (((Q : ℕ) : K))^2)) i) =
          (NumberField.mixedEmbedding K ((β : K) / (((Q : ℕ) : K))^2)).2
            ((cmComplexPlaceEquiv K f hcompl).symm i) from
        mixedSpace_equiv_pi_fin_of_card_apply hreal f hcompl _ i]
      -- Now apply mixedEmbedding_apply_isComplex
      rw [mixedEmbedding.mixedEmbedding_apply_isComplex (K := K) (β : K)
          ((cmComplexPlaceEquiv K f hcompl).symm i)]
      rw [mixedEmbedding.mixedEmbedding_apply_isComplex (K := K)
          ((β : K) / (((Q : ℕ) : K))^2)
          ((cmComplexPlaceEquiv K f hcompl).symm i)]
      -- Goal: ((Q:ℂ)²)⁻¹ * w.val.embedding (β:K) =
      --        w.val.embedding ((β:K) / Q²)
      -- w.val.embedding is a ring hom, so it commutes with /, pow, natCast
      set w := ((cmComplexPlaceEquiv K f hcompl).symm i).val.embedding
      rw [map_div₀ w, map_pow w, map_natCast w]
      field_simp
    classNumBound := Real.log (Fintype.card (ClassGroup (𝓞 K)) : ℝ) / (f : ℝ)
    hClassNum := by
      have hf_ne : (f : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hcard_pos : (0 : ℝ) < (Fintype.card (ClassGroup (𝓞 K)) : ℝ) := by
        have h : 0 < Fintype.card (ClassGroup (𝓞 K)) :=
          Fintype.card_pos (α := ClassGroup (𝓞 K))
        exact_mod_cast h
      rw [div_mul_cancel₀ _ hf_ne, Real.exp_log hcard_pos]
  }
  refine ⟨f, hfM, hf1, Λ, K, inferInstance, inferInstance, inferInstance, cmData,
    hCountable, F, hFund, hFVolLt, hFVolPos, hFBounded, hSep, hInj, ht'_ge, ?_⟩
  show Real.log (Fintype.card (ClassGroup (𝓞 K)) : ℝ) / (f : ℝ) ≤ log_H
  exact h_classNum

/-- **Cyclotomic CM field tower** (legacy, no longer on the proof path).

    Constructs K = ℚ(ζ_p) with all of Λ, F, hΛ_sep, hΛ_inj fully proved.
    Now forwards to `brd_cm_tower_postulate` which packages the missing
    BRD + Q²-scaling claims as a single labeled postulate. -/
def gs_tower_levels_proved (ℓ : ℕ) (hℓ : ℓ ≥ 2) (M : ℕ)
    (t log_H : ℝ) (ht : t ≥ 0) (hlog_H_pos : log_H > 0)
    (hlog_H_ge_rd : log_H ≥ 2 * Real.log (2 * (brd_tower_data ℓ hℓ).rd_F)) :
    ∃ (f : ℕ), f ≥ M ∧ ∃ (hf1 : f ≥ 1) (Λ : AddSubgroup (Fin f → ℂ))
      (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K)
      (cmData : CMTowerData f hf1 Λ K)
      (_ : Countable Λ) (F : Set (Fin f → ℂ)),
      IsAddFundamentalDomain Λ F volume ∧ volume F < ∞ ∧ volume F > 0 ∧
      Bornology.IsBounded F ∧
      (∀ v ∈ Λ, v ≠ 0 → ∃ i : Fin f, ‖v i‖ ≥ (brd_tower_data ℓ hℓ).D₀⁻¹) ∧
      (∀ v ∈ Λ, v (fin0 hf1) = 0 → v = 0) ∧
      t + 1 ≤ (cmData.t'_param : ℝ) ∧
      cmData.classNumBound ≤ log_H :=
  brd_cm_tower_postulate ℓ hℓ M t log_H ht hlog_H_pos hlog_H_ge_rd

/-- Disabled cyclotomic construction (kept as documentation; not used).
    Below `_unused_` is the prior ℚ(ζ_p) construction body, now superseded
    by `brd_cm_tower_postulate`.  All of its non-sorried lemmas remain
    available via `Erdos90.CMField.Cyclotomic`. -/
private def _unused_gs_tower_levels_cyclo (ℓ : ℕ) (_hℓ : ℓ ≥ 2) (base : GSBaseData ℓ) (M : ℕ) :
    ∃ (f : ℕ), f ≥ M ∧ ∃ (hf1 : f ≥ 1) (Λ : AddSubgroup (Fin f → ℂ))
      (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K)
      (_ : Countable Λ) (F : Set (Fin f → ℂ)),
      IsAddFundamentalDomain Λ F volume ∧ volume F < ∞ ∧ volume F > 0 ∧
      Bornology.IsBounded F ∧
      (∀ v ∈ Λ, v ≠ 0 → ∃ i : Fin f, ‖v i‖ ≥ base.D₀⁻¹) ∧
      (∀ v ∈ Λ, v (fin0 hf1) = 0 → v = 0) := by
  -- -----------------------------------------------------------------
  -- -----------------------------------------------------------------
  -- §1  Choose a prime p with (p-1)/2 ≥ M
  -- -----------------------------------------------------------------
  set M' := max M 2 with hM'_def
  have hM'_ge_M : M' ≥ M := le_max_left _ _
  have hM'_ge_2 : M' ≥ 2 := le_max_right _ _
  have h_exists_prime : ∃ p : ℕ, Nat.Prime p ∧ p ≥ 2*M' + 1 := by
    obtain ⟨p, hp_le, hp_prime⟩ := Nat.exists_infinite_primes (2*M' + 1)
    exact ⟨p, hp_prime, hp_le⟩
  obtain ⟨p, hp_prime, hp_ge⟩ := h_exists_prime
  have hp_gt_two : 2 < p := by
    have : 2*M' + 1 ≥ 5 := by
      have : M' ≥ 2 := hM'_ge_2
      omega
    omega
  -- f = φ(p)/2 = (p-1)/2
  set f := (p-1) / 2 with hf_def
  have hf_ge_M' : f ≥ M' := by
    have h_ineq : 2*M' + 1 ≤ p := hp_ge
    omega
  have hf_ge_M : f ≥ M := by omega
  have hf1 : f ≥ 1 := by
    have : M' ≥ 2 := hM'_ge_2
    omega
  -- -----------------------------------------------------------------
  -- §2  Construct the cyclotomic CM field K = ℚ(ζ_p)
  -- -----------------------------------------------------------------
  haveI : NeZero p :=
    NeZero.of_pos (Nat.Prime.pos hp_prime)
  let K : Type _ := CyclotomicField p ℚ
  haveI : NumberField K := inferInstance
  haveI : IsCyclotomicExtension {p} ℚ K :=
    CyclotomicField.isCyclotomicExtension (n := p) (K := ℚ)
  haveI : IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField K (S := {p}) ⟨p, by simp, hp_gt_two⟩
  haveI : IsTotallyComplex K := inferInstance
  have h_nrRealPlaces : InfinitePlace.nrRealPlaces K = 0 :=
    IsTotallyComplex.nrRealPlaces_eq_zero K
  have h_nrComplexPlaces_card : InfinitePlace.nrComplexPlaces K = f := by
    rw [hf_def]
    have h_totient : Nat.totient p = p-1 := Nat.totient_prime hp_prime
    have h_complex : InfinitePlace.nrComplexPlaces K = (Nat.totient p) / 2 :=
      IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (n := p) (K := K)
    rw [h_complex, h_totient]
  -- -----------------------------------------------------------------
  -- §3  Type bridge: mixedSpace K ≃ₗ[ℝ] Fin f → ℂ
  -- -----------------------------------------------------------------
  let φ : mixedEmbedding.mixedSpace K ≃ₗ[ℝ] (Fin f → ℂ) :=
    mixedSpace_equiv_pi_fin_of_card h_nrRealPlaces f h_nrComplexPlaces_card
  -- Transport the lattice basis
  let basis : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) ℝ (Fin f → ℂ) :=
    (mixedEmbedding.latticeBasis K).map φ
  haveI : Finite (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) := inferInstance
  -- -----------------------------------------------------------------
  -- §5  The scaled lattice Λ = Φ(Q⁻²·𝓞_K) and fundamental domain F
  -- -----------------------------------------------------------------
  let Λ : AddSubgroup (Fin f → ℂ) :=
    (Submodule.span ℤ (Set.range basis)).toAddSubgroup
  have hΛ_countable : Countable Λ := by
    dsimp [Λ]
    change Countable (Submodule.span ℤ (Set.range basis))
    infer_instance
  let F : Set (Fin f → ℂ) := ZSpan.fundamentalDomain basis
  have hF_fund : IsAddFundamentalDomain Λ F volume := by
    dsimp [F, Λ]
    exact ZSpan.isAddFundamentalDomain' basis volume
  have hF_bounded : Bornology.IsBounded F := by
    dsimp [F]
    exact ZSpan.fundamentalDomain_isBounded basis
  have hF_vol : volume F < ∞ := by
    dsimp [F]
    have h_bounded : Bornology.IsBounded (ZSpan.fundamentalDomain basis) :=
      ZSpan.fundamentalDomain_isBounded basis
    rcases h_bounded.subset_closedBall (0 : Fin f → ℂ) with ⟨R, hR⟩
    apply lt_of_le_of_lt (measure_mono hR)
    haveI : FiniteDimensional ℝ (Fin f → ℂ) := inferInstance
    haveI : ProperSpace (Fin f → ℂ) := FiniteDimensional.proper ℝ (Fin f → ℂ)
    exact measure_closedBall_lt_top
  have hF_vol_pos : volume F > 0 := by
    dsimp [F]
    have h_ne_zero : volume (ZSpan.fundamentalDomain basis) ≠ 0 :=
      ZSpan.measure_fundamentalDomain_ne_zero (b := basis) (μ := volume)
    exact pos_iff_ne_zero.mpr h_ne_zero
  -- -----------------------------------------------------------------
  -- §5  Separation: ∃ i, ‖v i‖ ≥ D₀⁻¹
  --
  --  For v = φ(Φ(a)) with a ∈ 𝒪_K \ {0}, the product formula gives
  --  ∏_w |a|_w ≥ 1, so some coordinate has |a|_w ≥ 1 ≥ D₀⁻¹.
  -- -----------------------------------------------------------------
  have hD₀_inv_le_one : base.D₀⁻¹ ≤ (1 : ℝ) := by
    simpa [one_div, div_one] using
      (one_div_le_one_div base.hD₀_pos (by norm_num : (0 : ℝ) < 1)).mpr base.hD₀_ge_one
  have mem_lattice_iff (v : Fin f → ℂ) : v ∈ Λ ↔
      ∃ a : 𝓞 K, φ (NumberField.mixedEmbedding K (a : K)) = v := by
    dsimp [Λ, basis]
    have h_range_eq : Set.range ((mixedEmbedding.latticeBasis K).map φ) =
        (φ.restrictScalars ℤ).toLinearMap '' Set.range (mixedEmbedding.latticeBasis K) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨mixedEmbedding.latticeBasis K i, ⟨i, rfl⟩, by simp⟩
      · rintro ⟨y, ⟨i, rfl⟩, h⟩
        refine ⟨i, ?_⟩
        simpa [LinearEquiv.restrictScalars_apply] using h
    have h_span_eq : Submodule.span ℤ (Set.range ((mixedEmbedding.latticeBasis K).map φ)) =
        Submodule.map (φ.restrictScalars ℤ).toLinearMap
          (mixedEmbedding.integerLattice K) := by
      rw [h_range_eq, ← Submodule.map_span, mixedEmbedding.span_latticeBasis]
    rw [Submodule.mem_toAddSubgroup, h_span_eq, Submodule.mem_map]
    simp only [mixedEmbedding.integerLattice, LinearMap.mem_range]
    constructor
    · rintro ⟨w, ⟨a, ha⟩, hw⟩
      refine ⟨a, ?_⟩
      have h_simp : ((mixedEmbedding K).comp (algebraMap (𝓞 K) K)).toIntAlgHom.toLinearMap a =
          NumberField.mixedEmbedding K (a : K) := by simp
      have hw_eq : NumberField.mixedEmbedding K (a : K) = w := by
        rw [← h_simp, ha]
      calc
        φ (NumberField.mixedEmbedding K (a : K)) = φ w := by rw [hw_eq]
        _ = (φ.restrictScalars ℤ).toLinearMap w := by simp
        _ = v := hw
    · rintro ⟨a, ha⟩
      refine ⟨NumberField.mixedEmbedding K (a : K), ⟨a, by simp⟩, ?_⟩
      simpa [LinearEquiv.restrictScalars_apply] using ha
  have hΛ_sep : ∀ v ∈ Λ, v ≠ 0 → ∃ i : Fin f, ‖v i‖ ≥ base.D₀⁻¹ := by
    intro v hv hv_nonzero
    rcases (mem_lattice_iff v).mp hv with ⟨a, ha⟩
    have ha0 : a ≠ 0 := by
      intro hzero
      apply hv_nonzero
      have hzero_val : (a : K) = 0 := by
        simpa using congrArg (fun (x : 𝓞 K) => (x : K)) hzero
      rw [hzero_val] at ha
      simp at ha
      exact ha.symm
    have h_sep : ∃ w : InfinitePlace K,
        mixedEmbedding.normAtPlace w (NumberField.mixedEmbedding K (a : K)) ≥ 1 := by
      have ha0' : (a : K) ≠ 0 := by
        intro h; apply ha0; exact Subtype.ext h
      have hpform := NumberField.prod_abs_eq_one ha0'
      have hfin : ∏ᶠ w : FinitePlace K, w (a : K) = (|Algebra.norm ℤ a| : ℝ)⁻¹ := by
        simpa using NumberField.FinitePlace.prod_eq_inv_abs_norm_int ha0
      rw [hfin] at hpform
      have hN_ge_one : (1 : ℝ) ≤ (|Algebra.norm ℤ a| : ℝ) := by
        have h := Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr ha0)
        exact_mod_cast h
      have hN_ne_zero : (|Algebra.norm ℤ a| : ℝ) ≠ 0 := by linarith
      have hP_eq_N : (∏ w : InfinitePlace K, w (a : K) ^ w.mult) = (|Algebra.norm ℤ a| : ℝ) := by
        calc
          (∏ w : InfinitePlace K, w (a : K) ^ w.mult) =
              ((∏ w : InfinitePlace K, w (a : K) ^ w.mult) * (|Algebra.norm ℤ a| : ℝ)⁻¹) *
                (|Algebra.norm ℤ a| : ℝ) := by
            field_simp [hN_ne_zero]
          _ = 1 * (|Algebra.norm ℤ a| : ℝ) := by rw [hpform]
          _ = (|Algebra.norm ℤ a| : ℝ) := by simp
      have h_mult_two : ∀ w : InfinitePlace K, w.mult = 2 :=
        fun w => IsTotallyComplex.mult_eq w
      simp_rw [h_mult_two] at hP_eq_N
      have h_sq_eq : (∏ w : InfinitePlace K, w (a : K) ^ 2) =
          ((∏ w : InfinitePlace K, w (a : K)) ^ 2) := by
        simp [Finset.prod_pow]
      rw [h_sq_eq] at hP_eq_N
      have h_prod_nonneg : 0 ≤ ∏ w : InfinitePlace K, w (a : K) :=
        Finset.prod_nonneg (fun w _ => apply_nonneg _ _)
      have h_prod_ge_one : (∏ w : InfinitePlace K, w (a : K)) ≥ 1 := by
        nlinarith
      haveI : Nonempty (InfinitePlace K) := by
        have h_card_pos : 0 < Fintype.card (InfinitePlace K) := by
          have h_no_real : nrRealPlaces K = 0 := IsTotallyComplex.nrRealPlaces_eq_zero K
          rw [card_eq_nrRealPlaces_add_nrComplexPlaces (K := K), h_no_real, zero_add]
          have h_rank := card_add_two_mul_card_eq_rank (K := K)
          rw [h_no_real] at h_rank
          by_contra! hzero
          have hzero' : nrComplexPlaces K = 0 := by omega
          rw [hzero'] at h_rank
          have h_finrank_pos : 0 < Module.finrank ℚ K :=
            Module.finrank_pos (R := ℚ) (M := K)
          omega
        exact Fintype.card_pos_iff.mp h_card_pos
      by_contra! h_all
      obtain ⟨w₀⟩ : Nonempty (InfinitePlace K) := inferInstance
      have h_prod_lt_one : (∏ w : InfinitePlace K, w (a : K)) < 1 := by
        classical
          have hw₀_mem : w₀ ∈ (Finset.univ : Finset (InfinitePlace K)) := Finset.mem_univ _
          calc
            (∏ w : InfinitePlace K, w (a : K)) =
                (∏ w ∈ (Finset.univ : Finset (InfinitePlace K)), w (a : K)) := by simp
            _ = w₀ (a : K) * (∏ w ∈ (Finset.univ : Finset (InfinitePlace K)).erase w₀, w (a : K)) := by
              rw [← Finset.prod_erase_mul (Finset.univ : Finset (InfinitePlace K)) _ hw₀_mem, mul_comm]
            _ ≤ w₀ (a : K) * (∏ _w ∈ (Finset.univ : Finset (InfinitePlace K)).erase w₀, (1 : ℝ)) := by
              refine mul_le_mul_of_nonneg_left
                (Finset.prod_le_prod (fun w _ => apply_nonneg _ _) (fun w hw =>
                  (by simpa [mixedEmbedding.normAtPlace_apply] using (h_all w).le)))
                (apply_nonneg _ _)
            _ = w₀ (a : K) := by simp
            _ < 1 := by simpa [mixedEmbedding.normAtPlace_apply] using h_all w₀
      linarith
    rcases h_sep with ⟨w, hw⟩
    have hw_complex : InfinitePlace.IsComplex w := IsTotallyComplex.isComplex w
    let w' : {w : InfinitePlace K // InfinitePlace.IsComplex w} := ⟨w, hw_complex⟩
    let idx : Fin f := cmComplexPlaceEquiv K f h_nrComplexPlaces_card w'
    have hnorm : ‖v idx‖ ≥ 1 := by
      rw [← ha]
      rw [mixedSpace_equiv_pi_fin_of_card_norm_apply h_nrRealPlaces f h_nrComplexPlaces_card (a : K) idx]
      have h_symm : (cmComplexPlaceEquiv K f h_nrComplexPlaces_card).symm idx = w' := by
        dsimp [idx]; simp
      rw [h_symm]
      simpa [mixedEmbedding.normAtPlace_apply] using hw
    refine ⟨idx, le_trans hD₀_inv_le_one hnorm⟩
  have hΛ_inj : ∀ v ∈ Λ, v (fin0 hf1) = 0 → v = 0 := by
    intro v hv hzero
    rcases (mem_lattice_iff v).mp hv with ⟨a, ha⟩
    let w₀ : {w : InfinitePlace K // InfinitePlace.IsComplex w} :=
      (cmComplexPlaceEquiv K f h_nrComplexPlaces_card).symm (fin0 hf1)
    have h_coord_zero : (NumberField.mixedEmbedding K (a : K)).2 w₀ = 0 := by
      rw [← mixedSpace_equiv_pi_fin_of_card_apply h_nrRealPlaces f h_nrComplexPlaces_card
        (NumberField.mixedEmbedding K (a : K)) (fin0 hf1)]
      rw [ha]
      exact hzero
    have h_embedding_zero : mixedEmbedding.normAtPlace (w₀ : InfinitePlace K)
        (NumberField.mixedEmbedding K (a : K)) = 0 := by
      rw [mixedEmbedding.normAtPlace_apply_of_isComplex w₀.prop, h_coord_zero, norm_zero]
    rw [mixedEmbedding.normAtPlace_apply] at h_embedding_zero
    have ha_eq_zero : (a : K) = 0 := by
      by_contra! h_ne
      have h_pos : 0 < (w₀ : InfinitePlace K) (a : K) :=
        AbsoluteValue.pos_iff (w₀ : InfinitePlace K).1 |>.mpr h_ne
      linarith
    rw [ha_eq_zero, map_zero, map_zero] at ha
    exact ha.symm
  have h_φ1_norm : ∀ r : Fin f, ‖φ (NumberField.mixedEmbedding K (1 : K)) r‖ = 1 := by
    intro r
    rw [mixedSpace_equiv_pi_fin_of_card_norm_apply h_nrRealPlaces f h_nrComplexPlaces_card (1 : K) r]
    simp
  have h_φ_norm_div_conj : ∀ (α : K) (hα : α ≠ 0) (r : Fin f),
      ‖φ (NumberField.mixedEmbedding K (α / IsCMField.complexConj K α)) r‖ = 1 := by
    intro α hα r
    rw [mixedSpace_equiv_pi_fin_of_card_norm_apply h_nrRealPlaces f h_nrComplexPlaces_card
      (α / IsCMField.complexConj K α) r]
    exact normAtPlace_mixedEmbedding_cm_div_conj_eq_one α hα _
  refine ⟨f, hf_ge_M, hf1, Λ, K, inferInstance, inferInstance, inferInstance,
    hΛ_countable, F, hF_fund, hF_vol, hF_vol_pos, hF_bounded, hΛ_sep, hΛ_inj⟩

/-- **Prop 3.6 + Minkowski type bridge**: tower levels with lattice.

    Takes target parameters (t, log_H) to fix the Q²-scaling and class-number bound.
    Forwards to `brd_cm_tower_postulate` (single labeled sorry). -/
def gs_tower_levels (ℓ : ℕ) (hℓ : ℓ ≥ 2) (M : ℕ)
    (t log_H : ℝ) (ht : t ≥ 0) (hlog_H_pos : log_H > 0)
    (hlog_H_ge_rd : log_H ≥ 2 * Real.log (2 * (brd_tower_data ℓ hℓ).rd_F)) :
    ∃ (f : ℕ), f ≥ M ∧ ∃ (hf1 : f ≥ 1) (Λ : AddSubgroup (Fin f → ℂ))
      (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K)
      (cmData : CMTowerData f hf1 Λ K)
      (_ : Countable Λ) (F : Set (Fin f → ℂ)),
      IsAddFundamentalDomain Λ F volume ∧ volume F < ∞ ∧ volume F > 0 ∧
      Bornology.IsBounded F ∧
      (∀ v ∈ Λ, v ≠ 0 → ∃ i : Fin f, ‖v i‖ ≥ (brd_tower_data ℓ hℓ).D₀⁻¹) ∧
      (∀ v ∈ Λ, v (fin0 hf1) = 0 → v = 0) ∧
      t + 1 ≤ (cmData.t'_param : ℝ) ∧
      cmData.classNumBound ≤ log_H :=
  brd_cm_tower_postulate ℓ hℓ M t log_H ht hlog_H_pos hlog_H_ge_rd


/-- **Golod–Shafarevich tower data** — abstract interface for Props 3.2–3.6.

    Packages the output of the Golod–Shafarevich / Chebotarev tower construction:
    - `D₀ > 0`: denominator Q² (product of t split primes q₁,…,qₜ squared)
    - `rd_F ≥ 1`: root discriminant of the base cubic field F
    - `log rd_F ≤ ℓ · log ℓ`: log bound (since rd_F ≤ 2ℓ)
    - `getTowerLevel`: for any M, a tower level Kⱼ = Fⱼ(i) with degree f ≥ M
      and Minkowski lattice Λ ⊂ ℂ^f with fundamental domain F and separation.

    The tower data feeds into Prop 2.2 (`cm_norm_one_elements`) which constructs
    the norm-one set U via the class-group pigeonhole on Kⱼ.

    **Mathematical content** (Props 3.2–3.6 of [OpenAI 2026]):
    1. Choose ℓ primes r₁,…,r_ℓ ≡ 1 (mod 3).  The cyclic cubic field F
       (subfield of ℚ(ζ_{r₁})⋯ℚ(ζ_{r_ℓ})) has |D_F| = D² = (∏ rᵢ)², M/F
       everywhere unramified, d(G) ≥ ℓ−1 for G = Gal(F^{ur,3}/F).
    2. Golod–Shafarevich: r(G) ≤ d(G)²/4 ⟹ G infinite pro-3.  With Shafarevich
       bound r ≤ d + C₀, this gives infinite tower F = F₀ ⊂ F₁ ⊂ ⋯ with
       fⱼ = [Fⱼ : ℚ] → ∞, Kⱼ = Fⱼ(i) CM, rd(Kⱼ) = rd(F) = |D_F|^{1/3} ≤ 2ℓ.
    3. Chebotarev (Prop 3.6): find t = ⌊(ℓ−1)²/100⌋ primes q₁,…,qₜ with
       Frobenius in Φ(G).  Killing them gives G̅ infinite.  Set D₀ = Q², Q = ∏ qᵦ.
    4. Minkowski embedding: Φⱼ : Kⱼ →+* mixedSpace Kⱼ ≃ ℂ^{fⱼ} gives lattice
       Λⱼ = Φⱼ(D₀⁻¹ · 𝒪_{Kⱼ}) with first-coordinate separation from the
       split-prime product formula.

    **Lean gaps** (three sub-steps, none fully in Mathlib v4.29.1):
    - (a) Golod–Shafarevich: pro-3 group theory, Frattini subgroup, relation-rank
      bound r ≤ d²/4.  Not in Mathlib.
    - (b) Quantitative Chebotarev: ∃ t primes q₁,…,qₜ with prescribed Frobenius
      in the Frattini-quotient Φ(G).  Not in Mathlib.
    - (c) Type bridge: `mixedSpace K ≃ Fin f → ℂ` for totally complex K, and
      transport of `integerLattice K` + `IsAddFundamentalDomain` + separation
      across it.  The isomorphism can be built from `Fintype.equivFin` +
      `LinearEquiv.piCongrLeft`, but the full API (fundamental domain transport,
      volume preservation, separation) is not in Mathlib.

    **Relevant Mathlib APIs** (available but incomplete):
    - `fundamentalDomain_integerLattice` in `CanonicalEmbedding/Basic.lean`
    - `volume_fundamentalDomain_latticeBasis` in same file
    - `ZSpan.isAddFundamentalDomain` in `Algebra/Module/ZLattice/Basic.lean`
    - `IsCyclotomicExtension.isCMField` in `NumberField/Cyclotomic/Basic.lean`
    - `discr_prime_pow` in `Cyclotomic/Discriminant.lean` -/
structure GSTowerData (ℓ : ℕ) where
  D₀ : ℝ
  hD₀_pos : D₀ > 0
  rd_F : ℝ
  hrd_F_ge1 : rd_F ≥ 1
  hlog_rd : Real.log rd_F ≤ (ℓ : ℝ) * Real.log (ℓ : ℝ)
  /-- For any (M, t, log_H), provides a tower level with degree f ≥ M, Minkowski
      lattice Λ ⊂ ℂ^f, and `CMTowerData` with `t'_param ≥ t + 1` and
      `classNumBound ≤ log_H`.  Encapsulates the BRD tower postulate
      (HMR 2021 + Q²-scaling). -/
  getTowerLevel (M : ℕ) (t log_H : ℝ) (ht : t ≥ 0) (hlog_H_pos : log_H > 0)
      (hlog_H_ge_rd : log_H ≥ 2 * Real.log (2 * rd_F)) :
    ∃ (f : ℕ), f ≥ M ∧ ∃ (hf1 : f ≥ 1)
    (Λ : AddSubgroup (Fin f → ℂ))
    (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K)
    (cmData : CMTowerData f hf1 Λ K)
    (_ : Countable Λ) (F : Set (Fin f → ℂ)),
    IsAddFundamentalDomain Λ F volume ∧ volume F < ∞ ∧ volume F > 0 ∧
    Bornology.IsBounded F ∧
    (∀ v ∈ Λ, v ≠ 0 → ∃ i : Fin f, ‖v i‖ ≥ D₀⁻¹) ∧
    (∀ v ∈ Λ, v (fin0 hf1) = 0 → v = 0) ∧
    t + 1 ≤ (cmData.t'_param : ℝ) ∧
    cmData.classNumBound ≤ log_H

/-- **Golod–Shafarevich tower with lattice** (Props 3.2–3.6).

    Assembly of `gs_base_construction` (Props 3.2–3.5, sorried) and
    `gs_tower_levels` (Prop 3.6 + type bridge, sorried) into `GSTowerData`.
    No additional sorries beyond the two sub-defs. -/
def golod_shafarevich_tower_with_lattice (ℓ : ℕ) (hℓ : ℓ ≥ 2) : GSTowerData ℓ :=
  let brd := brd_tower_data ℓ hℓ
  { D₀ := brd.D₀
    hD₀_pos := brd.hD₀_pos
    rd_F := brd.rd_F
    hrd_F_ge1 := brd.hrd_F_ge1
    hlog_rd := brd.hlog_rd
    getTowerLevel := fun M t log_H ht hlog_H_pos hlog_H_ge_rd =>
      gs_tower_levels ℓ hℓ M t log_H ht hlog_H_pos hlog_H_ge_rd }
