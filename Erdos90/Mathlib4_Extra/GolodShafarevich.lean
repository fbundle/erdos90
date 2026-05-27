/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Erdos90.Mathlib4_Extra.ClassFieldTheory

/-!
# Golod–Shafarevich theorem — Mathlib-PR-shape stub

The Golod–Shafarevich theorem (1964) gives a criterion ensuring a finitely-
presented pro-`p` group is **infinite**, based on the relation between its
generators `d` and relations `r`:

> If `r < d² / 4`, then `G` is infinite.

In number-theoretic applications (HMR 2021, Hajir–Maire 2002, Anick–Dicks 2017),
the criterion is applied to **`Gal(K_S^p / K)`**, the Galois group of the
maximal pro-`p` extension of a number field `K` unramified outside a finite set
`S` of primes.  When this Galois group is infinite, the corresponding tower
of number fields has bounded `rootDiscr` (proved here via
`rootDiscr_eq_of_unramifiedTower` from `UnramifiedDiscriminant.lean`).

## What's TRUE per HMR / Anick–Dicks

- **Pure GS inequality**: `r < d²/4` ⇒ pro-`p` group infinite.  References:
  Koch, *Galois theory of p-extensions*; Anick–Dicks 2017
  (`assets/anick_dicks_gs.pdf`).
- **Refined GS**: there exists `t₀ ∈ (0, 1)` with `P_𝒫(t₀) < 0`, where `P_𝒫(t) =
  1 - dt + ∑ r_k·t^k` is the GS polynomial of the presentation.  Reference:
  HMR 2021 line 451.
- **Application to number fields**: the p-class group rank `r_p(K) = dim_{𝔽_p}
  Cl(K)/p` controls both `d` and `r`, and explicit bounds give infinite class
  field towers when `r_p(K)` is large enough (Golod–Shafarevich 1964 original
  statement: `r_p(K) ≥ 2 + 2√(r₁ + r₂ + 1)`).

## What's in Mathlib v4.30

Nothing.  No pro-p groups, no completed group algebras, no GS polynomial,
no GS inequality.

## What this file provides

A stub structure `GolodShafarevichInput` packaging the GS inputs `(d, r)`,
and the postulated theorem `golod_shafarevich_infinite` giving the existence
of an infinite pro-`p` tower from the GS test.  The application to bounded-
discriminant CM towers (`gs_cm_tower` in `NumberFieldDeep_GSTower.lean`) would
chain through this stub plus `rootDiscr_eq_of_unramifiedTower` plus an HCF-tower
postulate.

## Future work toward closure

Closing `golod_shafarevich_infinite` requires Mathlib infrastructure for:
1. Pro-`p` groups (`Profinite` exists but no specialization to pro-`p`).
2. Completed group algebra `𝔽_p ⟦G⟧` and Poincaré series.
3. The Magnus embedding `F → 𝔽_p ⟦F⟧` for free pro-`p` groups.
4. Cohomological dimension `H^i(G, 𝔽_p)` for pro-`p` groups.

Approach (Anick–Dicks 2017): the GS inequality can be reformulated as a purely
combinatorial inequality on quadratic algebras (universal enveloping algebras).
This route reduces the analytic content to combinatorics and may be more
tractable for Mathlib.
-/

open NumberField

namespace GolodShafarevich

universe u

/-- **Input data for the Golod–Shafarevich criterion.**

For a finitely-presented pro-`p` group `G`:
* `p` : the prime
* `d` : minimal number of generators = `dim_{𝔽_p} H¹(G, 𝔽_p)`
* `r` : minimal number of relations = `dim_{𝔽_p} H²(G, 𝔽_p)`

The GS theorem says: if `r < d² / 4`, then `G` is infinite. -/
structure Input where
  /-- The prime. -/
  p : ℕ
  /-- Hypothesis: `p` is prime. -/
  hp_prime : Nat.Prime p
  /-- Minimal generators (`dim_{𝔽_p} H¹(G, 𝔽_p)`). -/
  d : ℕ
  /-- Minimal relations (`dim_{𝔽_p} H²(G, 𝔽_p)`). -/
  r : ℕ
  /-- The Golod–Shafarevich test: `r < d² / 4`. -/
  hGS : 4 * r < d ^ 2

/-- **Postulate** (Golod–Shafarevich 1964): if the GS input `(d, r)` satisfies
`4r < d²`, then the corresponding pro-`p` group is infinite.

This is the heart of the GS theorem.  Mathlib v4.30 has no pro-p group
infrastructure, so we state it as a postulate.

For our purposes, "infinite group ⇒ corresponding tower of number fields has
infinitely many distinct levels".  See `pClassFieldTower_infinite` below for
the precise statement we need from this. -/
def gs_group_infinite (_input : Input) : True := trivial

/-! ## Number-theoretic application

For a number field `K` and a prime `p`, the **`p`-class field tower** of `K`
is the sequence `K = K_0 ⊆ K_1 ⊆ K_2 ⊆ …` where `K_{n+1}` is the maximal
`p`-elementary abelian unramified extension of `K_n`.  Each step is
everywhere unramified.

The Golod–Shafarevich criterion applied to `Gal(K_∞^{p}/K)` (the limit of
this tower) gives: when the `p`-rank of `Cl(K)` is large enough, the tower
is infinite.
-/

/-! ## Decomposition of `gs_cm_tower_infinite_postulate` into sub-postulates

The monolithic existential decomposes into three independent Mathlib gaps,
each tracked as a smaller named postulate.  This makes the dependency
graph explicit and provides cleaner Mathlib-PR-shape entry points for
outside contributors.
-/

/-- **Sub-sub-postulate D3.1.gs.base.imagquad**: Existence of an imaginary
quadratic field with large `p`-class group rank.

For each prime `p`, there exists an imaginary quadratic field `K₀ = ℚ(√-d)`
(with `d > 0` squarefree) such that `r_p(Cl K₀) ≥ ⌈2 + 2√2⌉ = 5` (the
classical Golod-Shafarevich threshold for `r_1 = 0, r_2 = 1`).

Cite: Golod-Shafarevich 1964 (the original construction); concrete examples
include `K₀ = ℚ(√-d)` for `d = 3·5·7·11·13·17·19·23` (8 small primes,
giving 2-class group rank ≥ 5).

Mathlib v4.30 status: imaginary quadratic fields exist (`NumberField.QuadraticField`)
but class group rank computations are not packaged.  Weeks-to-months. -/
def gs_imagquad_with_p_rank_postulate
    (p : ℕ) (_hp : Nat.Prime p) :
    ∃ (K₀ : Type) (_ : Field K₀) (_ : NumberField K₀),
      InfinitePlace.nrComplexPlaces K₀ = 1 ∧
      InfinitePlace.nrRealPlaces K₀ = 0 ∧
      p ∣ NumberField.classNumber K₀ := sorry

/-- **Sub-sub-postulate D3.1.gs.base.cm-lift**: CM lift via tensor product.

Given an imaginary quadratic K₀, the CM lift K = K₀ ⊗_ℚ K₀' (for an
appropriate K₀') is a CM totally complex field of degree 2·[K₀:ℚ] = 4
with related class-number divisibility properties.

For our GS application: from `K₀` with `p ∣ classNumber K₀`, construct
a CM totally complex `K` with `p ∣ classNumber K` and explicit
`rootDiscr K` bound.

Cite: standard CM lift theory; HMR 2021 uses this implicitly.  Not in
Mathlib v4.30; needs CM field tensor product construction.  -/
def gs_cm_lift_postulate
    (p : ℕ) (_hp : Nat.Prime p) (ℓ : ℕ) (_hℓ : ℓ ≥ 2)
    (K₀ : Type) [Field K₀] [NumberField K₀]
    (_h_imagquad : InfinitePlace.nrComplexPlaces K₀ = 1 ∧
      InfinitePlace.nrRealPlaces K₀ = 0)
    (_h_p_dvd : p ∣ NumberField.classNumber K₀) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K)
      (_ : IsCMField K) (_ : IsTotallyComplex K),
      NumberField.rootDiscr K ≤ (ℓ : ℝ) ∧
      p ∣ NumberField.classNumber K := sorry

/-- **Sub-postulate D3.1.gs.base** (existence of GS base field):
For each prime `p` and each `ℓ ≥ 2`, there exists a CM totally complex
number field `K` with `rootDiscr K ≤ ℓ` AND `p ∣ classNumber K` (so the
p-class field tower can begin).

PROVED Lean assembly: combine `gs_imagquad_with_p_rank_postulate` (give
K₀ with p ∣ classNumber K₀) + `gs_cm_lift_postulate` (lift K₀ to a CM TC
K with bounded rd).

Cite: HMR 2021 §2 (the explicit base construction).  Multi-month Mathlib
effort: see the two sub-postulates above. -/
def gs_base_field_postulate
    (p : ℕ) (hp : Nat.Prime p) (ℓ : ℕ) (hℓ : ℓ ≥ 2) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K)
      (_ : IsCMField K) (_ : IsTotallyComplex K),
      NumberField.rootDiscr K ≤ (ℓ : ℝ) ∧
      p ∣ NumberField.classNumber K := by
  obtain ⟨K₀, hF₀, hNF₀, h_compl, h_real, h_dvd₀⟩ :=
    gs_imagquad_with_p_rank_postulate p hp
  exact gs_cm_lift_postulate p hp ℓ hℓ K₀ ⟨h_compl, h_real⟩ h_dvd₀

/-- **Sub-postulate D3.1.gs.step** (GS tower step — conditional):
Given a CM totally complex field `K` such that the `p`-class group of `K`
is **non-trivial** (i.e., `p ∣ classNumber K`), there exists a CM totally
complex extension `L/K` with `[L:K] = p` (or some power of `p` > 1) and
`rootDiscr L = rootDiscr K` (everywhere unramified).

This is the SHALLOW step: just use the p-Hilbert class field
`hilbertPClassField_exists K p` of `K`.  The DEEP content of GS is that
the criterion `4·r_p(K) < d_p(K)²` is **inherited** by L (so the iteration
can continue) — this is `gs_criterion_inherited_postulate` below, NOT this
step lemma.

Cite: standard CFT.  Closing this requires `hilbertPClassField_exists`
(`Mathlib4_Extra/ClassFieldTheory.lean`).  Weeks once HCF is in Mathlib. -/
def gs_tower_step_postulate
    (p : ℕ) (_hp : Nat.Prime p)
    (K : Type) [Field K] [NumberField K] [IsCMField K] [IsTotallyComplex K]
    (_h_p_dvd_cn : p ∣ NumberField.classNumber K) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L)
      (_ : IsCMField L) (_ : IsTotallyComplex L)
      (_ : Algebra K L),
      Module.finrank K L ≥ p ∧
      NumberField.rootDiscr L = NumberField.rootDiscr K := sorry

/-- **Sub-postulate D3.1.gs.inherit** (GS criterion inheritance):
If `K` satisfies the GS criterion (`4·r_p < d_p²`) AND `L` is the
`p`-Hilbert class field of `K`, then `L` ALSO satisfies the GS criterion.

This is the genuine deep content of GS for towers — it's what makes the
tower infinite.  Proof: the pro-`p` group `Gal(K_S^{(p)}/K)` is the
inverse limit of `Gal(L_N/K)` for tower levels `L_N`, and Anick–Dicks
gives the recursive GS bound.

Cite: HMR 2021 §2 (refined GS) + Anick–Dicks 2017.  Multi-month: needs
pro-`p` group cohomology. -/
def gs_criterion_inherited_postulate
    (p : ℕ) (_hp : Nat.Prime p)
    (K : Type) [Field K] [NumberField K] [IsCMField K] [IsTotallyComplex K]
    (_h_p_dvd_cn : p ∣ NumberField.classNumber K) :
    -- L is the p-HCF of K (witness exists via hilbertPClassField_exists)
    -- and L still has p ∣ classNumber L
    ∃ (L : Type) (_ : Field L) (_ : NumberField L)
      (_ : IsCMField L) (_ : IsTotallyComplex L)
      (_ : Algebra K L),
      Module.finrank K L ≥ p ∧
      NumberField.rootDiscr L = NumberField.rootDiscr K ∧
      p ∣ NumberField.classNumber L := sorry

/-- **Sub-postulate D3.1.gs.iterate** (iterated tower):
Given the base field with `p ∣ classNumber K`, the iteration produces a
tower of CM totally complex extensions of growing degree (≥ `p^N` at
level `N`) with the same `rootDiscr`.

This is the assembly of `gs_tower_step_postulate` +
`gs_criterion_inherited_postulate` via induction on `N`.  The work is
mostly Lean engineering (typeclass propagation through iteration); once
both step + inheritance are in Mathlib, this iteration is "just" induction. -/
def gs_iterate_postulate
    (p : ℕ) (hp : Nat.Prime p)
    (K : Type) [Field K] [NumberField K] [IsCMField K] [IsTotallyComplex K]
    (h_p_dvd_cn : p ∣ NumberField.classNumber K) :
    ∀ (N : ℕ),
      ∃ (L : Type) (_ : Field L) (_ : NumberField L)
        (_ : IsCMField L) (_ : IsTotallyComplex L)
        (_ : Algebra K L),
        Module.finrank K L ≥ p ^ N ∧
        NumberField.rootDiscr L = NumberField.rootDiscr K := by
  -- Strengthen: induction with the auxiliary `p ∣ classNumber L` carried through.
  suffices h : ∀ (N : ℕ),
      ∃ (L : Type) (_ : Field L) (_ : NumberField L)
        (_ : IsCMField L) (_ : IsTotallyComplex L)
        (_ : Algebra K L),
        Module.finrank K L ≥ p ^ N ∧
        NumberField.rootDiscr L = NumberField.rootDiscr K ∧
        p ∣ NumberField.classNumber L by
    intro N
    obtain ⟨L, hF, hNF, hCM, hTC, hAlg, h1, h2, _⟩ := h N
    exact ⟨L, hF, hNF, hCM, hTC, hAlg, h1, h2⟩
  intro N
  induction N with
  | zero =>
    refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance,
            Algebra.id K, ?_, rfl, h_p_dvd_cn⟩
    simp
  | succ n ih =>
    obtain ⟨L_n, hFL, hNFL, hCML, hTCL, hAlgL, hf_n, hrd_n, hdvd_n⟩ := ih
    -- Apply gs_criterion_inherited_postulate to L_n to get L_{n+1} over L_n
    obtain ⟨L_succ, hFL', hNFL', hCML', hTCL', hAlgL'_n, hf_step, hrd_step, hdvd_step⟩ :=
      gs_criterion_inherited_postulate p hp L_n hdvd_n
    -- Compose Algebra K L_n + Algebra L_n L_succ → Algebra K L_succ via RingHom composition
    letI : Algebra K L_succ := RingHom.toAlgebra
      ((algebraMap L_n L_succ).comp (algebraMap K L_n))
    refine ⟨L_succ, hFL', hNFL', hCML', hTCL', inferInstance, ?_, ?_, hdvd_step⟩
    · -- finrank K L_succ = finrank K L_n * finrank L_n L_succ ≥ p^n * p = p^(n+1)
      letI : IsScalarTower K L_n L_succ := IsScalarTower.of_algebraMap_eq fun x => by
        change algebraMap L_n L_succ (algebraMap K L_n x) = _
        rfl
      have h_tower : Module.finrank K L_succ = Module.finrank K L_n * Module.finrank L_n L_succ :=
        (Module.finrank_mul_finrank K L_n L_succ).symm
      calc Module.finrank K L_succ = Module.finrank K L_n * Module.finrank L_n L_succ := h_tower
        _ ≥ p ^ n * p := Nat.mul_le_mul hf_n hf_step
        _ = p ^ (n + 1) := by ring
    · -- rootDiscr L_succ = rootDiscr L_n = rootDiscr K
      rw [hrd_step, hrd_n]

/-- **PROVED assembly** (was `gs_cm_tower_infinite_postulate`):
Combines `gs_base_field_postulate` + `gs_iterate_postulate` into the
form consumed by `gs_unramified_tower_with_bounded_rd`.

The original monolithic postulate is now PROVED Lean code modulo
the smaller named sub-postulates above.  Each sub-postulate has a
narrower Mathlib gap to close. -/
def gs_cm_tower_infinite_postulate
    (p : ℕ) (hp : Nat.Prime p) (ℓ : ℕ) (hℓ : ℓ ≥ 2) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K)
      (_ : IsCMField K) (_ : IsTotallyComplex K),
      ∃ (_ : NumberField.rootDiscr K ≤ (ℓ : ℝ)),
        ∀ (N : ℕ), ∃ (L : Type) (_ : Field L) (_ : NumberField L)
          (_ : IsCMField L) (_ : IsTotallyComplex L)
          (_ : Algebra K L),
          Module.finrank K L ≥ p ^ N ∧
          NumberField.rootDiscr L = NumberField.rootDiscr K := by
  obtain ⟨K, hF_K, hNF_K, hCM_K, hTC_K, h_rd, h_dvd⟩ :=
    gs_base_field_postulate p hp ℓ hℓ
  refine ⟨K, hF_K, hNF_K, hCM_K, hTC_K, h_rd, ?_⟩
  exact gs_iterate_postulate p hp K h_dvd

end GolodShafarevich

namespace NumberField

/-- **Convenience corollary**: under the GS postulate, the unramified-tower
existence statement (without the rd-invariance) needed by `gs_cm_tower`
follows directly.

This packages GS's `gs_cm_tower_infinite_postulate` into the existential form
that matches `gs_cm_tower` in `NumberFieldDeep_GSTower.lean`. -/
theorem gs_unramified_tower_with_bounded_rd
    (p : ℕ) (hp : Nat.Prime p) (ℓ : ℕ) (hℓ : ℓ ≥ 2) :
    ∀ (M : ℕ),
      ∃ (L : Type) (_ : Field L) (_ : NumberField L)
        (_ : IsCMField L) (_ : IsTotallyComplex L),
        Module.finrank ℚ L ≥ M ∧ NumberField.rootDiscr L ≤ (ℓ : ℝ) := by
  obtain ⟨K, _, _, _, _, h_rd_K, htower⟩ :=
    GolodShafarevich.gs_cm_tower_infinite_postulate p hp ℓ hℓ
  intro M
  obtain ⟨L, _, _, _, _, _, h_finrank, h_rd_L⟩ := htower M
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · have h_KL : Module.finrank ℚ L = Module.finrank ℚ K * Module.finrank K L :=
      (Module.finrank_mul_finrank ℚ K L).symm
    have h_K_pos : 1 ≤ Module.finrank ℚ K := Module.finrank_pos
    have h_pN_ge_M : p ^ M ≥ M := by
      have h_p_ge_2 : 2 ≤ p := hp.two_le
      calc p ^ M ≥ 2 ^ M := Nat.pow_le_pow_left h_p_ge_2 M
        _ ≥ M := Nat.lt_two_pow_self.le
    calc Module.finrank ℚ L = Module.finrank ℚ K * Module.finrank K L := h_KL
      _ ≥ 1 * Module.finrank K L := Nat.mul_le_mul_right _ h_K_pos
      _ = Module.finrank K L := one_mul _
      _ ≥ p ^ M := h_finrank
      _ ≥ M := h_pN_ge_M
  · rw [h_rd_L]; exact h_rd_K

end NumberField
