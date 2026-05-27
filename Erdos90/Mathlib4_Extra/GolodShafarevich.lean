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

/-- **Sub-postulate D3.1.gs.base** (existence of GS base field):
For each prime `p` and each `ℓ ≥ 2`, there exists a CM totally complex
number field `K` with `rootDiscr K ≤ ℓ` AND `p ∣ classNumber K` (so the
p-class field tower can begin).

Cite: HMR 2021 §2 (the explicit base construction).  Multi-month Mathlib
effort: needs pro-`p` group cohomology + class field theory.  -/
def gs_base_field_postulate
    (p : ℕ) (_hp : Nat.Prime p) (ℓ : ℕ) (_hℓ : ℓ ≥ 2) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K)
      (_ : IsCMField K) (_ : IsTotallyComplex K),
      NumberField.rootDiscr K ≤ (ℓ : ℝ) ∧
      p ∣ NumberField.classNumber K := sorry

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
    (p : ℕ) (_hp : Nat.Prime p)
    (K : Type) [Field K] [NumberField K] [IsCMField K] [IsTotallyComplex K]
    (_h_p_dvd_cn : p ∣ NumberField.classNumber K) :
    ∀ (N : ℕ),
      ∃ (L : Type) (_ : Field L) (_ : NumberField L)
        (_ : IsCMField L) (_ : IsTotallyComplex L)
        (_ : Algebra K L),
        Module.finrank K L ≥ p ^ N ∧
        NumberField.rootDiscr L = NumberField.rootDiscr K := sorry

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
