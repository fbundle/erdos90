/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Mathlib

/-!
# Discriminant in unramified tower extensions

For a tower of number fields `L/K/ℚ` where `L/K` is everywhere unramified,
the discriminant satisfies `|discr L| = |discr K|^[L:K]`, hence
`rootDiscr L = rootDiscr K`.

This is the key tool used in the Hajir–Maire–Ramakrishna 2021 construction
to control root discriminants up an infinite tower (one of the inputs to
`gs_cm_tower` in `Erdos90/NumberFieldDeep_GSTower.lean`).

## Main results

* `NumberField.differentIdeal_eq_top_of_isUnramifiedAt` — if every nonzero
  prime of `𝓞 L` is unramified over `𝓞 K`, then the different ideal is `⊤`.
* `NumberField.natAbs_discr_eq_pow_of_unramifiedTower` — discriminant tower
  formula for unramified extensions: `|discr L| = |discr K|^[L:K]`.
* `NumberField.rootDiscr_eq_of_unramifiedTower` — corollary:
  `rootDiscr L = rootDiscr K`.

## References

- Mathlib `RingTheory/DedekindDomain/Different.lean` for the
  `not_dvd_differentIdeal_iff` bridge and the
  `natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`
  discriminant tower formula.
- HMR 2021 §2: "root discriminants are constant in unramified extensions"
  (line 293 of `assets/hmr_2021_src/Cutting_towers_arxiv.tex`).
-/

namespace NumberField

open Ideal

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L]

attribute [local instance] FractionRing.liftAlgebra in
/-- If every nonzero prime of `𝓞 L` is unramified over `𝓞 K`, then the
different ideal of `𝓞 L / 𝓞 K` is the unit ideal. -/
theorem differentIdeal_eq_top_of_isUnramifiedAt
    (h : ∀ (P : Ideal (𝓞 L)) [P.IsPrime], P ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) P) :
    differentIdeal (𝓞 K) (𝓞 L) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨M, hM_max, hI_le⟩ := Ideal.exists_le_maximal _ hne
  have hM_prime : M.IsPrime := hM_max.isPrime
  have hM_ne_bot : M ≠ ⊥ := by
    intro hM_bot
    rw [hM_bot, ← Ideal.zero_eq_bot] at hI_le
    exact differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L) (le_bot_iff.mp hI_le)
  have h_unram : Algebra.IsUnramifiedAt (𝓞 K) M := h M hM_ne_bot
  have h_not_dvd : ¬ M ∣ differentIdeal (𝓞 K) (𝓞 L) :=
    (not_dvd_differentIdeal_iff (A := 𝓞 K) (B := 𝓞 L) (P := M)).mpr h_unram
  exact h_not_dvd (Ideal.dvd_iff_le.mpr hI_le)

attribute [local instance] FractionRing.liftAlgebra in
/-- For a tower of number fields `L/K` that is everywhere unramified
(at every nonzero prime of `𝓞 L`), the discriminant of `L` is the
discriminant of `K` raised to the relative degree:
`|discr L| = |discr K|^[L:K]`. -/
theorem natAbs_discr_eq_pow_of_unramifiedTower
    (h : ∀ (P : Ideal (𝓞 L)) [P.IsPrime], P ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) P) :
    (discr L).natAbs = (discr K).natAbs ^ Module.finrank K L := by
  have h_diff_top : differentIdeal (𝓞 K) (𝓞 L) = ⊤ :=
    differentIdeal_eq_top_of_isUnramifiedAt K L h
  have h_tower := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (K := K) (𝒪 := 𝓞 K) L (𝓞 L)
  rw [h_diff_top, Ideal.absNorm_top, one_mul] at h_tower
  exact h_tower

/-- **Root discriminant is constant in unramified extensions.**

For a tower of number fields `L/K` that is everywhere unramified
(at every nonzero prime of `𝓞 L`), `rootDiscr L = rootDiscr K`.

This is the discriminant-control input for the Hajir–Maire–Ramakrishna
2021 infinite CM tower construction: starting from a base field of
bounded root discriminant, every unramified extension preserves the
root discriminant bound.

Cite: HMR 2021 line 293 of `assets/hmr_2021_src/Cutting_towers_arxiv.tex`.
-/
theorem rootDiscr_eq_of_unramifiedTower
    (h : ∀ (P : Ideal (𝓞 L)) [P.IsPrime], P ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) P) :
    rootDiscr L = rootDiscr K := by
  have h_finrank : Module.finrank ℚ L =
      Module.finrank ℚ K * Module.finrank K L :=
    (Module.finrank_mul_finrank ℚ K L).symm
  have h_discr := natAbs_discr_eq_pow_of_unramifiedTower K L h
  rw [rootDiscr_def, rootDiscr_def, h_finrank]
  have h_finrank_pos_K : (0 : ℝ) < Module.finrank ℚ K :=
    Nat.cast_pos.mpr Module.finrank_pos
  have h_finrank_pos_KL : (0 : ℝ) < Module.finrank K L :=
    Nat.cast_pos.mpr Module.finrank_pos
  -- Goal: |↑(discr L)|^... = |↑(discr K)|^...
  -- where `|↑(discr L)| = ((discr L).natAbs : ℝ)` via norm_cast lemmas.
  simp only [← Nat.cast_natAbs] at *
  -- Now both sides use `((natAbs ·) : ℝ)` form, no more `|·|`.
  have hcast : ((discr L).natAbs : ℝ) =
      ((discr K).natAbs : ℝ) ^ (Module.finrank K L : ℕ) := by
    exact_mod_cast congrArg ((↑) : ℕ → ℝ) h_discr
  rw [hcast]
  have h_K_nonneg : 0 ≤ ((discr K).natAbs : ℝ) := Nat.cast_nonneg _
  rw [← Real.rpow_natCast (((discr K).natAbs : ℝ)) (Module.finrank K L),
    ← Real.rpow_mul h_K_nonneg]
  congr 1
  rw [Nat.cast_mul]
  field_simp

end NumberField
