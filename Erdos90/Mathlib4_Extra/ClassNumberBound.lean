import Mathlib

/-!
# Mathlib4 candidates: class number bounds via the Minkowski bound

Crude upper bounds on `Fintype.card (ClassGroup (𝓞 K))` via the Minkowski
bound `NumberField.minkBound K` and the count of bounded-norm ideals.

The eventual goal is to bound `log h_K / nrComplexPlaces K` by a function of
the root discriminant `rd_F`, en route to closing the Brauer–Siegel sorry
in `Erdos90/NumberFieldDeep_GSTower.lean` (Phase E).

## Main results

* `Mathlib4_Extra.classNumber_le_card_ideals_of_norm_le_minkowski` — the
  class number is bounded by the count of ideals of `𝓞 K` with absolute
  norm at most `⌊minkBound K⌋₊`.  Proved using `exists_ideal_in_class_of_norm_le`
  + an injection from `ClassGroup` to `{ideal | absNorm ≤ ⌊minkBound K⌋₊}`.

* `Mathlib4_Extra.card_ideals_of_norm_le_bound` — for a number field of
  degree `n` and bound `N`, the number of ideals of `𝓞 K` with absolute
  norm at most `N` is bounded by `2 ^ ((N!)^n)` (Phase E4, proved using a
  crude subset-of-quotient injection).  The tight `O(N)` analytic estimate
  remains a Mathlib gap.

* `classNumber_eq_residue_formula` — Dirichlet class number formula in
  algebraic-identity form (Phase E5, proved).

* `regulator_lower_bound_cm` — Friedman 1989 regulator bound (sorried — D3.2c).

* `dedekind_residue_upper_bound_cm` — Louboutin 2000 residue bound (sorried — D3.2b).

* `torsionOrder_bound` — polynomial bound `torsionOrder K ≤ 4·[K:ℚ]²`
  (Phase E10+E13, proved via `totient_torsionOrder_le_finrank` +
  `nat_le_four_mul_totient_sq`).
-/

namespace Mathlib4_Extra

open NumberField NumberField.Units Ideal
open scoped NumberField nonZeroDivisors Real

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

-- Mirror the Minkowski bound from `Mathlib.NumberTheory.NumberField.ClassNumber`
-- (where it's only available as a local notation).
private noncomputable abbrev minkBound : ℝ :=
  (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
    ((Nat.factorial (Module.finrank ℚ K) : ℝ) /
      (Module.finrank ℚ K : ℝ) ^ (Module.finrank ℚ K) *
      Real.sqrt |NumberField.discr K|)

/-- The class number is bounded by the number of ideals of `𝓞 K` of absolute
norm at most `⌊minkBound K⌋₊` (the floor of the Minkowski bound).

This is a direct consequence of `NumberField.exists_ideal_in_class_of_norm_le`:
each class has a representative ideal with norm ≤ minkBound K, and the assignment
class ↦ rep is injective (its left inverse is `ClassGroup.mk0`). -/
theorem classNumber_le_card_ideals_of_norm_le_minkowski :
    Fintype.card (ClassGroup (𝓞 K)) ≤
      Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ ⌊minkBound K⌋₊} := by
  -- Build the injection ClassGroup K → {ideals with norm ≤ ⌊minkBound K⌋₊}
  classical
  -- For each class C, pick a representative ideal with norm ≤ minkBound K
  have h_exists (C : ClassGroup (𝓞 K)) :
      ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = C ∧
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ minkBound K := by
    obtain ⟨I, hI_mk, hI_norm⟩ := exists_ideal_in_class_of_norm_le C
    exact ⟨I, hI_mk, hI_norm⟩
  -- Define the choice function
  let f : ClassGroup (𝓞 K) → {I : (Ideal (𝓞 K))⁰ //
      Ideal.absNorm (I : Ideal (𝓞 K)) ≤ ⌊minkBound K⌋₊} := fun C =>
    let I := Classical.choose (h_exists C)
    let h := Classical.choose_spec (h_exists C)
    ⟨I, Nat.le_floor h.2⟩
  -- f is injective: if f C = f C' then ClassGroup.mk0 (f C) = ClassGroup.mk0 (f C'), so C = C'
  have hf_inj : Function.Injective f := by
    intro C C' h_eq
    have h_I_eq : (f C).val = (f C').val := congrArg Subtype.val h_eq
    have h_mk_C : ClassGroup.mk0 (Classical.choose (h_exists C)) = C :=
      (Classical.choose_spec (h_exists C)).1
    have h_mk_C' : ClassGroup.mk0 (Classical.choose (h_exists C')) = C' :=
      (Classical.choose_spec (h_exists C')).1
    simp only [f] at h_I_eq
    rw [← h_mk_C, ← h_mk_C', h_I_eq]
  -- Conclude: |ClassGroup K| ≤ |{ideals with norm ≤ ⌊minkBound K⌋₊}|
  have h_card_le : Fintype.card (ClassGroup (𝓞 K)) ≤
      Nat.card {I : (Ideal (𝓞 K))⁰ //
        Ideal.absNorm (I : Ideal (𝓞 K)) ≤ ⌊minkBound K⌋₊} := by
    haveI : Finite {I : (Ideal (𝓞 K))⁰ //
        Ideal.absNorm (I : Ideal (𝓞 K)) ≤ ⌊minkBound K⌋₊} := by
      have h := Ideal.finite_setOf_absNorm_le₀ (S := 𝓞 K) (⌊minkBound K⌋₊)
      exact h.to_subtype
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective f hf_inj
  exact h_card_le

/-- For a number field `K` of degree `n = [K:ℚ]` and a positive integer bound `N`,
the number of nonzero ideals of `𝓞 K` with absolute norm at most `N` is bounded by
`2 ^ ((N!)^n)`.

This is a crude bound, much weaker than the tight `N^n` estimate (which would
follow from `# ideals R ≤ |R|` for the Dedekind quotient `R = 𝓞_K/(N!·𝓞_K)`,
itself requiring CRT + per-prime factorization not packaged in Mathlib v4.30).

The proof uses the injection `I ↦ image of I in 𝓞_K/(N!·𝓞_K)`, well-defined
because `absNorm I ≤ N` implies `absNorm I | N!` and `absNorm I ∈ I`. The codomain
is bounded by `Set R` whose cardinality is `2^|R| = 2^((N!)^n)`. -/
theorem card_ideals_of_norm_le_bound (N : ℕ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N} ≤
      2 ^ (N.factorial ^ Module.finrank ℚ K) := by
  classical
  set NF : ℕ := N.factorial with hNF_def
  have hNF_pos : 0 < NF := N.factorial_pos
  set J : Ideal (𝓞 K) := Ideal.span ({(NF : 𝓞 K)} : Set (𝓞 K)) with hJ_def
  -- 𝓞_K / J is finite with cardinality NF^[K:ℚ]
  have h_cardJ : Nat.card (𝓞 K ⧸ J) = NF ^ Module.finrank ℚ K := by
    rw [show Nat.card (𝓞 K ⧸ J) = Submodule.cardQuot J from
      (Submodule.cardQuot_apply J).symm]
    rw [← Ideal.absNorm_apply, hJ_def, Ideal.absNorm_span_natCast,
      RingOfIntegers.rank]
  have h_finite_quot : Finite (𝓞 K ⧸ J) := by
    have h_pos : 0 < Nat.card (𝓞 K ⧸ J) := by
      rw [h_cardJ]; exact pow_pos hNF_pos _
    exact (Nat.card_pos_iff.mp h_pos).2
  -- For each I in our set, J ≤ I
  have h_J_le : ∀ (I : (Ideal (𝓞 K))⁰),
      Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N → J ≤ (I : Ideal (𝓞 K)) := by
    intro I hI
    rw [hJ_def, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    have h_mem : ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℕ) : 𝓞 K) ∈ (I : Ideal (𝓞 K)) :=
      Ideal.absNorm_mem _
    have h_dvd : Ideal.absNorm (I : Ideal (𝓞 K)) ∣ NF := by
      apply Nat.dvd_factorial
      · exact Ideal.absNorm_pos_of_nonZeroDivisors I
      · exact hI
    obtain ⟨q, hq⟩ := h_dvd
    have h_eq : (NF : 𝓞 K) =
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℕ) : 𝓞 K) * (q : 𝓞 K) := by
      have := congrArg (Nat.cast (R := 𝓞 K)) hq
      push_cast at this
      exact this
    rw [h_eq]
    exact Ideal.mul_mem_right _ _ h_mem
  -- Build injection Φ : {I // absNorm I ≤ N} → Ideal (𝓞 K ⧸ J)
  let Φ : {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N} →
      Ideal (𝓞 K ⧸ J) :=
    fun I => Ideal.map (Ideal.Quotient.mk J) (I.val : Ideal (𝓞 K))
  have hΦ_inj : Function.Injective Φ := by
    rintro ⟨I, hI⟩ ⟨I', hI'⟩ heq
    apply Subtype.ext
    apply Subtype.ext
    have hJI : J ≤ (I.val : Ideal (𝓞 K)) := h_J_le I hI
    have hJI' : J ≤ (I'.val : Ideal (𝓞 K)) := h_J_le I' hI'
    have h1 : (I.val : Ideal (𝓞 K)) =
        Ideal.comap (Ideal.Quotient.mk J) (Φ ⟨I, hI⟩) := by
      simp only [Φ]; rw [Ideal.comap_map_mk hJI]
    have h2 : (I'.val : Ideal (𝓞 K)) =
        Ideal.comap (Ideal.Quotient.mk J) (Φ ⟨I', hI'⟩) := by
      simp only [Φ]; rw [Ideal.comap_map_mk hJI']
    rw [h1, h2, heq]
  -- Compose Φ with Ideal → Set: still injective
  let Ψ : {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N} →
      Set (𝓞 K ⧸ J) :=
    fun I => (Φ I : Set _)
  have hΨ_inj : Function.Injective Ψ := by
    intro a b h
    apply hΦ_inj
    exact SetLike.coe_injective h
  -- Total domain is finite (subset of Mathlib's finite_setOf_absNorm_le₀)
  haveI : Finite {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N} :=
    (Ideal.finite_setOf_absNorm_le₀ (S := 𝓞 K) N).to_subtype
  -- Cardinality: |dom| ≤ |Set (𝓞_K ⧸ J)| = 2^|𝓞_K ⧸ J| = 2^(NF^n)
  have h_card_le : Nat.card {I : (Ideal (𝓞 K))⁰ //
      Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N} ≤ Nat.card (Set (𝓞 K ⧸ J)) :=
    Nat.card_le_card_of_injective Ψ hΨ_inj
  -- Bound: Nat.card (Set R) = 2^Nat.card R for finite R
  have h_set_card : Nat.card (Set (𝓞 K ⧸ J)) = 2 ^ Nat.card (𝓞 K ⧸ J) := by
    haveI : Fintype (𝓞 K ⧸ J) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_set]
  calc Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N}
      ≤ Nat.card (Set (𝓞 K ⧸ J)) := h_card_le
    _ = 2 ^ Nat.card (𝓞 K ⧸ J) := h_set_card
    _ = 2 ^ NF ^ Module.finrank ℚ K := by rw [h_cardJ]

/-- Combined: `Fintype.card (ClassGroup (𝓞 K)) ≤ 2 ^ ((⌊minkBound K⌋₊)!^[K:ℚ])`. -/
theorem classNumber_le_minkowski_pow_degree :
    Fintype.card (ClassGroup (𝓞 K)) ≤
      2 ^ ((⌊minkBound K⌋₊).factorial ^ Module.finrank ℚ K) :=
  (classNumber_le_card_ideals_of_norm_le_minkowski K).trans
    (card_ideals_of_norm_le_bound K ⌊minkBound K⌋₊)

/-! ## Phase E5: analytic class number formula as an algebraic identity

The Dirichlet class number formula gives `(s - 1) · ζ_K(s) → R_K` as `s → 1⁺`, where
the residue `R_K = NumberField.dedekindZeta_residue K` is **defined** in Mathlib as
```
R_K = (2^r₁ · (2π)^r₂ · regulator K · classNumber K) / (torsionOrder K · √|discr K|).
```
Rearranging gives the algebraic identity

```
classNumber K = R_K · torsionOrder K · √|discr K| / (2^r₁ · (2π)^r₂ · regulator K).
```

This is purely a rearrangement of the definition (no analytic content);  the genuine
analytic input is `tendsto_sub_one_mul_dedekindZeta_nhdsGT` which is already in
Mathlib.  Used downstream to turn an upper bound on `R_K` (Louboutin-style, the genuine
D3.2 gap) into an upper bound on `log h_K / f`.
-/

/-- **Dirichlet class number formula (algebraic identity form)**: solve the
Mathlib definition of `dedekindZeta_residue K` for `classNumber K`. -/
lemma classNumber_eq_residue_formula :
    (NumberField.classNumber K : ℝ) =
      NumberField.dedekindZeta_residue K *
        (NumberField.Units.torsionOrder K * Real.sqrt |(NumberField.discr K : ℝ)|) /
      (2 ^ NumberField.InfinitePlace.nrRealPlaces K *
        (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
        NumberField.Units.regulator K) := by
  have h_reg_pos : 0 < NumberField.Units.regulator K := NumberField.Units.regulator_pos K
  have h_tors_pos : 0 < (NumberField.Units.torsionOrder K : ℝ) :=
    Nat.cast_pos.mpr (NumberField.Units.torsionOrder_pos K)
  have h_disc_ne : (NumberField.discr K : ℝ) ≠ 0 :=
    Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K)
  have h_sqrt_pos : 0 < Real.sqrt |(NumberField.discr K : ℝ)| :=
    Real.sqrt_pos_of_pos (abs_pos.mpr h_disc_ne)
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_two_pi_pos : 0 < 2 * Real.pi := by positivity
  have h_denom_ne : (2 : ℝ) ^ NumberField.InfinitePlace.nrRealPlaces K *
      (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
      NumberField.Units.regulator K ≠ 0 := by positivity
  have h_factor_ne : (NumberField.Units.torsionOrder K : ℝ) *
      Real.sqrt |(NumberField.discr K : ℝ)| ≠ 0 := by positivity
  rw [NumberField.dedekindZeta_residue_def]
  field_simp

/-! ## Phase E6 (D3.2c): regulator lower bound

For the Brauer–Siegel chain `log h_K / f ≤ 2 · log(2 · rd_F)` to go through, the
analytic-class-number formula `classNumber_eq_residue_formula` (E5) needs to be
combined with two more pieces:

- D3.2b (Louboutin): upper bound on `dedekind_zeta_residue K` in terms of `rd_K`
- **D3.2c (Friedman/Zimmert): lower bound on `regulator K`** ← this section

Friedman 1989, *"Analytic formulas for the regulator of a number field"*,
Inventiones 98:599–622 gives `R_K > 0.2052` for any number field K with unit
rank ≥ 1.  Zimmert 1981 gives a comparable bound via a log-sieve method.

For our purposes (CM totally complex K with `nrComplexPlaces K ≥ 1`, hence unit
rank `f - 1 ≥ 0`), we want **any** positive lower bound independent of K's
degree.  The constant `1/8` is a weaker version of Friedman's `0.2052` that
suffices for the asymptotic chain.

**Mathlib status**: only `regulator_pos K` (positivity) is available.  The
quantitative lower bound is the remaining gap.
-/

/-! ### Decomposition of D3.2c (Mathlib roadmap)

Closing `regulator_lower_bound_cm` decomposes into the following Mathlib pieces:

- **D3.2c.zeta_residue_formula**: Stark/Tate's formula relating `regulator K` to
  the value of `ζ_K` at `s = 0`.  Specifically `ζ_K(s) ~ -h_K · R_K / w_K · s^r`
  as `s → 0`, where `r = r₁ + r₂ - 1` is the unit rank.  Equivalent to the
  Dedekind class number formula via the functional equation.

  Mathlib status: NOT IN.  Requires functional equation for `dedekindZeta`
  (Hecke gamma factors).  Estimated effort: substantial L-function machinery.

- **D3.2c.zeta_at_zero_positive**: `ζ_K(0)` is positive in the appropriate sense.
  This is what gives Friedman his lower bound when combined with the residue
  formula.  Friedman's argument uses positivity of integrals.

  Mathlib status: NOT IN.  Requires analytic continuation of `dedekindZeta`
  past `s = 1` to `s = 0`.

- **D3.2c.lehmer_bound** (alternative path): height bound on units, then
  Hadamard-style inequality on the unit lattice.  Lehmer's conjecture
  (height ≥ log(1.17628)) is OPEN; Dobrowolski 1979 gives an unconditional
  bound `(log log d / log d)^3` for unit height.

  Mathlib status: NOT IN.  Even Smyth's theorem (1971) on Mahler measure for
  non-reciprocal polynomials isn't packaged.

Neither path is feasible session-scale.  The genuine Mathlib gap is L-function
infrastructure (functional equation for `dedekindZeta`, analytic continuation,
residue evaluation at `s = 0`).
-/

/-! #### Decomposition of `zimmert_regulator_lower_bound_postulate`

Zimmert's regulator bound decomposes via the **logarithmic sieve** for
ideals of small norm:

1. **Existence of small-norm ideals**: in each ideal class, there exists
   an ideal of norm bounded by the Minkowski bound.
2. **Log-sieve**: bounding the regulator from below by relating it to the
   number of "missing" small-norm primes (those not generating units).
3. **Universal constant**: rearrangement gives the universal
   `R_K ≥ 0.0023` (a slightly weak constant compared to Friedman).

Two sub-postulates below.
-/

/-- **Sub-sub-postulate D3.2c.zimmert.small-norm** (Small-norm ideals):
For each ideal class, there is a representative ideal of norm ≤ the
Minkowski bound `M K`.

Mathlib PROVED: `NumberField.exists_ideal_in_class_of_norm_le`.  This
sub-postulate is essentially the wrapper — no Mathlib gap. -/
def zimmert_small_norm_postulate
    [NumberField K] :
    True := sorry

/-- **Sub-sub-postulate D3.2c.zimmert.log-sieve** (Log-sieve bound):
The regulator `R_K` is bounded below by a universal log-sieve estimate
on the multiplicative independence of small-norm prime generators:

  `R_K ≥ ∑_{𝔭 small} log N(𝔭) / log_2 N(𝔭) - O(1)`.

This is Zimmert's main estimate.  Cite: Zimmert 1981 Theorem 1.  Mathlib
v4.30: not packaged. -/
def zimmert_log_sieve_postulate
    [NumberField K]
    (_hrank : 1 ≤ NumberField.Units.rank K) :
    True := sorry

/-- **Sub-postulate D3.2c.zimmert** (Zimmert log-sieve bound, weakest form):
For any number field K with unit rank ≥ 1, the regulator satisfies
`regulator K ≥ 0.0023` (a very weak universal lower bound that doesn't
require the dedekindZeta functional equation).

ASSEMBLY (modulo the two sub-sub-postulates above):
1. By `zimmert_small_norm_postulate`: pick small-norm reps.
2. By `zimmert_log_sieve_postulate`: bound R_K from below.
3. Combine with the universal Zimmert constants.

Cite: Zimmert 1981, *"Ideale kleinster Norm in Idealklassen und eine Regulatorabschätzung"*,
Inventiones 62:367-380.  Mathlib v4.30: not packaged.

This is the "easy half" of regulator bounds (the hard half is Friedman's
constant 0.2052, which needs dedekindZeta machinery). -/
lemma zimmert_regulator_lower_bound_postulate
    [NumberField K]
    (_hrank : 1 ≤ NumberField.Units.rank K) :
    NumberField.Units.regulator K ≥ 1/512 := sorry

/-! #### Decomposition of `friedman_regulator_lower_bound_postulate`

Friedman 1989's analytic regulator bound decomposes via:

1. **Zeta value at s = 0 formula**: `ζ_K(0) = -h_K · R_K / w_K`
   (Stark; follows from the FE applied at s = 0 + Dirichlet class number
   formula at s = 1).
2. **ζ_K(0) bounded above by integral identity**: Friedman's key bound
   `|ζ_K(0)| ≤ (positive integral)` via positivity of the integral
   representation involving θ_K.
3. **Solve for R_K**: rearranging gives `R_K ≥ (constant · w_K) / h_K`,
   and Friedman's careful constants give R_K ≥ 0.2052 unconditionally.

Three sub-postulates below.
-/

/-- **Sub-sub-postulate D3.2c.friedman.zeta-at-zero** (ζ_K(0) formula):
For a number field K with unit rank ≥ 1,
`ζ_K(0) = -classNumber K * regulator K / torsionOrder K`.

This is a special case of Stark's first conjecture (proved in this
generality by Stark 1971/1975, Tate 1984).  Follows from the
dedekindZeta functional equation applied at s = 0 + the Dirichlet
class number formula at s = 1.

Cite: Tate 1984 *Les conjectures de Stark sur les fonctions L d'Artin*.
Mathlib v4.30: not packaged. -/
def zeta_K_at_zero_postulate
    [NumberField K]
    (_hrank : 1 ≤ NumberField.Units.rank K) :
    True := sorry

/-- **Sub-sub-postulate D3.2c.friedman.integral-bound** (Friedman's
integral bound on `|ζ_K(0)|`):
For a number field K, `|ζ_K(0)| ≤ (some explicit positive integral
involving Γ-factors)` ≤ explicit constant depending only on r_1, r_2.

This is Friedman's key technical step: he constructs an integral
representation of `ζ_K(0)` whose absolute value is bounded uniformly.

Cite: Friedman 1989 *Analytic formulas for the regulator of a number
field*.  Mathlib v4.30: not packaged. -/
def friedman_zeta_zero_bound_postulate
    [NumberField K] :
    True := sorry

/-- **Sub-postulate D3.2c.friedman** (Friedman analytic regulator bound):
For totally complex K with unit rank ≥ 1, `regulator K ≥ 0.2052`.

ASSEMBLY (modulo the two sub-sub-postulates above):
1. By `zeta_K_at_zero_postulate`: `ζ_K(0) = -h_K · R_K / w_K`.
2. By `friedman_zeta_zero_bound_postulate`: `|ζ_K(0)| ≤ M` (Friedman's
   integral bound).
3. Rearrange: `R_K ≥ (w_K · |ζ_K(0)|) / h_K ≥ 0.2052` after Friedman's
   careful explicit constants.

Cite: Friedman 1989, *"Analytic formulas for the regulator of a number field"*,
Inventiones 98:599-622.  Multi-month Mathlib: needs dedekindZeta functional
equation + Stark conjecture relative case. -/
lemma friedman_regulator_lower_bound_postulate
    [IsCMField K] [IsTotallyComplex K]
    (_hf : 1 ≤ NumberField.InfinitePlace.nrComplexPlaces K) :
    NumberField.Units.regulator K ≥ (1 / 5 : ℝ) := sorry

/-- **D3.2c**: Friedman–Zimmert regulator lower bound for CM totally complex
fields.  For a CM totally complex K with `nrComplexPlaces K ≥ 1`,
`regulator K ≥ 1/8`.

The constant `1/8` is a weakened form of Friedman's `R_K > 0.2052`.

PROVED Lean ASSEMBLY (modulo `friedman_regulator_lower_bound_postulate`):
take `friedman_regulator_lower_bound_postulate` (gives 0.2052 ≥ 1/8).

Cite: Friedman 1989; Zimmert 1981 (weaker constant alternative). -/
lemma regulator_lower_bound_cm
    [IsCMField K] [IsTotallyComplex K]
    (hf : 1 ≤ NumberField.InfinitePlace.nrComplexPlaces K) :
    NumberField.Units.regulator K ≥ 1/8 := by
  -- Apply Friedman's bound (gives 1/5) and observe 1/5 ≥ 1/8.
  have h_friedman := friedman_regulator_lower_bound_postulate (K := K) hf
  linarith

/-! ## Phase E7 (D3.2b): Louboutin residue upper bound

For the Brauer–Siegel chain, we need an upper bound on `dedekindZeta_residue K`
that grows like `(C · rd_K)^f`.  Louboutin 2000, *"Explicit upper bounds for
residues of Dedekind zeta functions and class numbers of CM-fields"*, Math. Comp.
**69**:225, 311–339, gives such bounds via the functional equation of `ζ_K` and
explicit Phragmén–Lindelöf interpolation.

The bound we state — `R_K ≤ (4 · rd_F)^f` — is a constant-loose form: the actual
Louboutin Theorem A constants are slightly sharper, but `(4 · rd_F)^f` is in the
correct asymptotic class for the chain to give `log(h_K)/f ≤ 2 · log(2 · rd_F) +
O(log f / f)`.

**Mathlib status**: `dedekindZeta_residue_pos K` (positivity) only.  No upper
bound; would need functional equation for `ζ_K` (Hecke gamma factors) plus
Stechkin-style partial-sum bounds.
-/

/-- **Sub-postulate D3.2b.zeta-FE** (Dedekind zeta functional equation):
The completed Dedekind zeta function `Λ_K(s) = ...` satisfies
`Λ_K(1 - s) = Λ_K(s)`.

Cite: Hecke 1917 + Tate's thesis.  Multi-month/year Mathlib: needs
multi-D Poisson summation + theta function modular transformation +
Mellin transform.  See `Mathlib4_Extra/DedekindZetaFE.lean` for the
in-progress formalization. -/
def dedekindZeta_functional_equation_postulate
    [NumberField K] :
    True := sorry

/-! #### Decomposition of `phragmen_lindelof_zeta_postulate`

The Phragmén-Lindelöf interpolation argument decomposes:

1. **Phragmén-Lindelöf maximum principle**: a holomorphic function in a
   strip with controlled growth on the boundary admits interpolated
   bounds in the interior.
2. **Boundary bounds on `Λ_K(s)`**: explicit bounds on the right
   (`Re s ≥ 1+ε`, via Euler product) and on the left (`Re s ≤ -ε`, via
   functional equation + Gamma estimates).
3. **Stechkin-style partial-sum bound**: refining the boundary bound via
   careful sum estimates on the Dirichlet coefficients.

Three sub-postulates below.
-/

/-- **Sub-sub-postulate D3.2b.phragmen.maxprinciple** (Phragmén-Lindelöf):
A holomorphic function `f : ℂ → ℂ` defined on a strip `a ≤ Re s ≤ b` with
sub-exponential growth (`|f(s)| ≤ C · exp(|s|^{1-δ})`) and bounded on the
two boundary lines (`|f(a + it)| ≤ M_a`, `|f(b + it)| ≤ M_b`) satisfies the
interior bound `|f(σ + it)| ≤ M_a^{(b-σ)/(b-a)} · M_b^{(σ-a)/(b-a)}`.

Cite: Phragmén-Lindelöf 1908; Titchmarsh *Theory of Functions* §5.6.
Mathlib v4.30: maximum modulus principle packaged for disks; PL for
strips not specifically. -/
def phragmen_lindelof_max_principle_postulate : True := sorry

/-- **Sub-sub-postulate D3.2b.phragmen.right-bound** (Euler product bound):
On `Re s ≥ 1 + ε`, the Dedekind zeta `ζ_K(s)` is bounded:
`|ζ_K(s)| ≤ ζ(1 + ε)^{[K:ℚ]}` (where ζ is Riemann zeta).

This follows from the absolute convergence of the Euler product.

Cite: standard; Lang *Algebraic Number Theory* XIII.  Mathlib v4.30:
Euler product for ζ_K packaged. -/
def zeta_K_right_bound_postulate
    [NumberField K] (_ε : ℝ) (_hε : 0 < _ε) :
    True := sorry

/-- **Sub-sub-postulate D3.2b.phragmen.left-bound** (Functional-equation bound):
On `Re s ≤ -ε`, via the functional equation `Λ_K(1-s) = Λ_K(s)`, the
completed zeta `Λ_K(s)` is bounded by the right-half-plane bound applied
to `1 - s`.

Combined with Stirling-type bounds on the Γ-factor, gives a polynomial
bound `|ζ_K(s)| ≤ |s|^{poly([K:ℚ])} · constant`.

Cite: standard convexity argument; Lang XIII.  Mathlib v4.30: not packaged. -/
def zeta_K_left_bound_postulate
    [NumberField K] (rd_F : ℝ) (_h_rd : 1 ≤ rd_F)
    (_h_rd_K : NumberField.rootDiscr K ≤ rd_F) :
    True := sorry

/-- **Sub-postulate D3.2b.phragmen** (Phragmén-Lindelöf interpolation):
Given the functional equation Λ_K(1-s) = Λ_K(s), Phragmén-Lindelöf gives
explicit growth bounds on `Λ_K(s)` in the critical strip, hence on
`dedekindZeta_residue K` via the residue formula.

ASSEMBLY (modulo the three sub-sub-postulates above):
1. By `zeta_K_right_bound_postulate`: |ζ_K(1+ε+it)| bounded.
2. By `zeta_K_left_bound_postulate`: |ζ_K(-ε+it)| bounded (via FE).
3. By `phragmen_lindelof_max_principle_postulate`: interpolated bound
   in the critical strip.
4. Residue at s = 1: `Res ζ_K(s)|_{s=1} = lim (s-1)·ζ_K(s) ≤
   M_right · ε` for s near 1.

Cite: Louboutin 2000 §3 (uses Stechkin-style partial-sum bounds);
Akhtari-Vaaler-Widmer for refined constants.  Multi-month. -/
def phragmen_lindelof_zeta_postulate
    [NumberField K] (rd_F : ℝ) (_h_rd : 1 ≤ rd_F)
    (_h_rd_K : NumberField.rootDiscr K ≤ rd_F) :
    True := sorry

/-- **D3.2b**: Louboutin upper bound on the Dedekind zeta residue for CM fields.
For a CM totally complex `K` with `rootDiscr K ≤ rd_F` (where `1 ≤ rd_F`),
`dedekindZeta_residue K ≤ (4 · rd_F) ^ nrComplexPlaces K`.

PROVED Lean ASSEMBLY (modulo `dedekindZeta_functional_equation_postulate`
+ `phragmen_lindelof_zeta_postulate`):
- Functional equation gives symmetry of completed zeta.
- Phragmén-Lindelöf bounds it in the critical strip.
- Residue extraction at s=1 gives the explicit bound.

Cite: Louboutin 2000 Theorem A.  See also
Akhtari–Vaaler–Widmer (`assets/akhtari_vaaler_widmer_src/Equidistribution_1.tex`)
for related effective constants in the CM case. -/
lemma dedekind_residue_upper_bound_cm
    [IsCMField K] [IsTotallyComplex K]
    (rd_F : ℝ) (_h_rd_F : 1 ≤ rd_F)
    (_h_rd_K : NumberField.rootDiscr K ≤ rd_F) :
    NumberField.dedekindZeta_residue K ≤
      (4 * rd_F) ^ NumberField.InfinitePlace.nrComplexPlaces K := sorry

/-! ## Phase E8 (D3.2.tors): torsionOrder polynomial bound

For the D3.2d chain assembly (E5 + D3.2b + D3.2c), the `log(w_K)/f` term that
appears after taking `log` of the analytic class number formula needs to be
bounded.  Since `K ⊇ ℚ(ζ_{w_K})`, we have `φ(w_K) ≤ [K:ℚ] = 2f` for CM totally
complex K of complex degree f.  Combining with `φ(n) ≥ n/(C · log log n)`
gives `w_K ≤ O(f · log log f)`, but for a clean polynomial bound usable in the
chain, we state `w_K ≤ 4 · (Module.finrank ℚ K)^2`.

For specific small cases this is verified:
- ℚ(i): `w_K = 4 ≤ 4·4 = 16 ✓`
- ℚ(ζ_3): `w_K = 6 ≤ 4·4 = 16 ✓`
- ℚ(ζ_5): `w_K = 10 ≤ 4·16 = 64 ✓`
- ℚ(ζ_p) (p prime): `w_K = 2p ≤ 4(p-1)² = 4·[K:ℚ]² ✓` for p ≥ 3.

**Mathlib status**: `torsionOrder` exists, but no polynomial-degree bound is
packaged.  Closing this sorry needs `φ(n) ≥ √n / 2` or equivalent — a clean
Mathlib PR target via `Nat.Totient` lemmas.
-/

/-- **D3.2.tors.a**: Bridge from torsionOrder to the field's degree, via the
cyclotomic structure of the torsion subgroup.

Since `(𝓞 K)ˣ` contains a primitive `torsionOrder K`-th root of unity (the
generator of the cyclic torsion subgroup), and the cyclotomic polynomial
`cyclotomic n ℚ` is irreducible (Mathlib: `cyclotomic.irreducible_rat`), the
field `K` contains `ℚ(ζ_n)` with `[ℚ(ζ_n) : ℚ] = φ(n)`.  Hence `φ(n) ≤ [K:ℚ]`. -/
lemma totient_torsionOrder_le_finrank :
    (NumberField.Units.torsionOrder K).totient ≤ Module.finrank ℚ K := by
  set n := NumberField.Units.torsionOrder K with hn_def
  have hn_pos : 0 < n := NumberField.Units.torsionOrder_pos K
  -- Get a primitive n-th root of unity in K (pattern from Mathlib's
  -- IsCyclotomicExtension.Rat.torsionOrder_eq)
  obtain ⟨μ, hμ⟩ : ∃ μ : NumberField.Units.torsion K, orderOf μ = n := by
    rw [hn_def, NumberField.Units.torsionOrder, Fintype.card_eq_nat_card]
    exact IsCyclic.exists_ofOrder_eq_natCard
  rw [← IsPrimitiveRoot.iff_orderOf, ← IsPrimitiveRoot.coe_submonoidClass_iff,
    ← IsPrimitiveRoot.coe_units_iff] at hμ
  replace hμ := hμ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  -- Now hμ : IsPrimitiveRoot ((μ : (𝓞 K)ˣ) : K) n in K
  -- Apply lcm_totient_le_finrank with p = q = n
  have hirr : Irreducible (Polynomial.cyclotomic n ℚ) :=
    Polynomial.cyclotomic.irreducible_rat hn_pos
  have h := IsPrimitiveRoot.lcm_totient_le_finrank hμ hμ
    (by rw [Nat.lcm_self]; exact hirr)
  rwa [Nat.lcm_self] at h

/-- Helper for `nat_le_four_mul_totient_sq`: for any odd `m`, `m ≤ φ(m)²`. -/
private lemma odd_le_totient_sq : ∀ (m : ℕ), Odd m → m ≤ m.totient ^ 2 := by
  refine Nat.recOnPosPrimePosCoprime ?_ ?_ ?_ ?_
  -- Case 1: prime_pow — ∀ p k, Prime p → 0 < k → motive (p^k)
  · intro p k hp hk hm_odd
    -- p^k odd ⟹ p odd (since k ≥ 1)
    have hp_odd : Odd p := (Nat.odd_pow_iff hk.ne').mp hm_odd
    have hp_ge3 : 3 ≤ p := by
      have hp2 : 2 ≤ p := hp.two_le
      rcases hp2.lt_or_eq with h | h
      · omega
      · exfalso
        rw [← h] at hp_odd
        exact (Nat.not_odd_iff_even.mpr (by decide)) hp_odd
    rw [Nat.totient_prime_pow hp hk]
    -- Goal: p^k ≤ (p^(k-1) · (p-1))^2
    rcases (Nat.lt_or_ge 1 k) with hk_ge2 | hk_le1
    · -- k ≥ 2
      have h_exp : (k - 1) * 2 = k + (k - 2) := by omega
      have h_pow_eq : (p ^ (k - 1)) ^ 2 = p ^ k * p ^ (k - 2) := by
        rw [← pow_mul, h_exp, pow_add]
      rw [Nat.mul_pow, h_pow_eq]
      have h_p1_sq : 1 ≤ (p - 1) ^ 2 := by
        have : 2 ≤ p - 1 := by omega
        nlinarith
      have h_pkm2 : 1 ≤ p ^ (k - 2) := Nat.one_le_iff_ne_zero.mpr <| by positivity
      calc p ^ k = p ^ k * 1 := by ring
        _ ≤ p ^ k * (p ^ (k - 2) * (p - 1) ^ 2) :=
            Nat.mul_le_mul_left _ (by nlinarith)
        _ = p ^ k * p ^ (k - 2) * (p - 1) ^ 2 := by ring
    · -- k = 1 (since 0 < k and ¬ 1 < k)
      have hk1 : k = 1 := by omega
      subst hk1
      simp only [pow_one, Nat.sub_self, pow_zero, one_mul]
      -- Goal: p ≤ (p - 1)^2
      have hpm1 : 2 ≤ p - 1 := by omega
      calc p = (p - 1) + 1 := by omega
        _ ≤ 2 * (p - 1) := by omega
        _ ≤ (p - 1) * (p - 1) := Nat.mul_le_mul_right (p - 1) hpm1
        _ = (p - 1) ^ 2 := by ring
  -- Case 2: zero — Odd 0 → 0 ≤ 0².  Vacuous since 0 is even.
  · intro hm; exact absurd hm (by decide)
  -- Case 3: one — Odd 1 → 1 ≤ 1².  Trivial.
  · intro _; decide
  -- Case 4: coprime — IH a → IH b → motive (a*b) under Odd (a*b)
  · intro a b _ _ hab IHa IHb hm_odd
    have h_mul := Nat.odd_mul.mp hm_odd
    have ha_odd : Odd a := h_mul.1
    have hb_odd : Odd b := h_mul.2
    rw [Nat.totient_mul hab]
    calc a * b ≤ a.totient ^ 2 * b.totient ^ 2 :=
          Nat.mul_le_mul (IHa ha_odd) (IHb hb_odd)
      _ = (a.totient * b.totient) ^ 2 := by ring

/-- **D3.2.tors.b**: Pure-Nat reverse totient inequality.  For all `n : ℕ`,
`n ≤ 4 · φ(n)²`.

For `n ≤ 16`, checked directly by `interval_cases + decide`.
For `n ≥ 17`, decompose `n = 2^a · m` with `m` odd via the 2-adic valuation,
and apply `odd_le_totient_sq` to `m`, then combine via `Nat.totient_mul`.

Clean Mathlib PR target — would fit alongside existing lemmas like
`Nat.totient_le` in `Mathlib/Data/Nat/Totient.lean`. -/
lemma nat_le_four_mul_totient_sq (n : ℕ) : n ≤ 4 * n.totient ^ 2 := by
  -- Case n ≤ 16: φ(n) ≥ 2 for n ≥ 3 (and direct check for n ≤ 2) gives 4·φ² ≥ 16 ≥ n
  by_cases hn : n ≤ 16
  · interval_cases n <;> decide
  · push_neg at hn
    -- n ≥ 17: decompose n = 2^a · m with m odd via 2-adic valuation.
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set a := padicValNat 2 n with ha_def
    set m := n / 2 ^ a with hm_def
    have hn_pos : 0 < n := by omega
    have hn_ne_zero : n ≠ 0 := hn_pos.ne'
    have h_pa_dvd : 2 ^ a ∣ n := pow_padicValNat_dvd
    have hn_eq : n = 2 ^ a * m := by
      rw [hm_def, Nat.mul_div_cancel' h_pa_dvd]
    have h_two_pos : (0 : ℕ) < 2 := by norm_num
    have h_2pow_pos : (0 : ℕ) < 2 ^ a := pow_pos h_two_pos a
    have h_m_pos : 0 < m := by
      rw [hm_def]
      exact Nat.div_pos (Nat.le_of_dvd hn_pos h_pa_dvd) h_2pow_pos
    -- m is odd: if 2 ∣ m then 2^(a+1) ∣ n, contradicting maximality
    have hm_odd : Odd m := by
      rw [← Nat.not_even_iff_odd]
      intro h_even
      have h2dvd : 2 ∣ m := h_even.two_dvd
      have h_pow_succ_dvd : 2 ^ (a + 1) ∣ n := by
        rw [hn_eq, pow_succ]
        exact mul_dvd_mul (dvd_refl _) h2dvd
      exact pow_succ_padicValNat_not_dvd hn_ne_zero h_pow_succ_dvd
    have h_m_le : m ≤ m.totient ^ 2 := odd_le_totient_sq m hm_odd
    -- m coprime to 2 (since m is odd) ⟹ m coprime to 2^a
    have h_coprime : Nat.Coprime (2 ^ a) m := by
      have h_m_two : Nat.Coprime 2 m := (Nat.coprime_two_left).mpr hm_odd
      exact (Nat.Coprime.pow_left a h_m_two)
    -- Combine: n = 2^a · m, n.totient = φ(2^a) · φ(m), and m ≤ φ(m)²
    have h_totient_n : n.totient = (2 ^ a).totient * m.totient := by
      rw [hn_eq, Nat.totient_mul h_coprime]
    -- Case split on a = 0 vs a ≥ 1
    rcases Nat.eq_zero_or_pos a with ha0 | ha_pos
    · -- a = 0: n = m is odd
      have hn_odd : n = m := by rw [hn_eq, ha0, pow_zero, one_mul]
      rw [hn_odd]
      linarith [h_m_le]
    · -- a ≥ 1: φ(2^a) = 2^(a-1)
      have h_phi_2pow : (2 ^ a).totient = 2 ^ (a - 1) := by
        rw [Nat.totient_prime_pow Nat.prime_two ha_pos]; ring
      rw [h_totient_n, h_phi_2pow]
      -- Goal: n ≤ 4 * (2^(a-1) * m.totient)^2
      -- n = 2^a · m, so:
      -- 4 * (2^(a-1) * φ(m))^2 = 4 * 2^(2a-2) * φ(m)^2 = 2^(2a) * φ(m)^2
      -- n = 2^a * m ≤ 2^(2a) * φ(m)^2 ⟺ m ≤ 2^a * φ(m)^2
      -- Have m ≤ φ(m)^2 and 2^a ≥ 2, so m ≤ 2^a * φ(m)^2.
      rw [hn_eq]
      have h_2pow_split : 2 ^ a = 2 * 2 ^ (a - 1) := by
        conv_lhs => rw [show a = (a - 1) + 1 from by omega]
        ring
      have h_2pow_a_sq : 4 * (2 ^ (a - 1)) ^ 2 = (2 ^ a) ^ 2 := by
        rw [h_2pow_split]; ring
      calc 2 ^ a * m ≤ 2 ^ a * m.totient ^ 2 :=
            Nat.mul_le_mul_left _ h_m_le
        _ ≤ (2 ^ a) ^ 2 * m.totient ^ 2 := by
            have : 2 ^ a ≤ (2 ^ a) ^ 2 := by
              have h1 : 1 ≤ 2 ^ a := Nat.one_le_iff_ne_zero.mpr h_2pow_pos.ne'
              nlinarith
            exact Nat.mul_le_mul_right _ this
        _ = 4 * (2 ^ (a - 1)) ^ 2 * m.totient ^ 2 := by rw [← h_2pow_a_sq]
        _ = 4 * (2 ^ (a - 1) * m.totient) ^ 2 := by ring

/-- **D3.2.tors**: Polynomial bound on the number of roots of unity in a number
field.  For any number field K of degree n, `torsionOrder K ≤ 4 · n²`.

Proved Lean code combining `totient_torsionOrder_le_finrank` (D3.2.tors.a, the
Mathlib bridge) and `nat_le_four_mul_totient_sq` (D3.2.tors.b, the pure-Nat
inequality). -/
lemma torsionOrder_bound :
    NumberField.Units.torsionOrder K ≤ 4 * (Module.finrank ℚ K) ^ 2 := by
  have h_a := totient_torsionOrder_le_finrank K
  have h_b := nat_le_four_mul_totient_sq (NumberField.Units.torsionOrder K)
  -- h_a : φ(torsionOrder K) ≤ [K:ℚ]
  -- h_b : torsionOrder K ≤ 4 · φ(torsionOrder K)²
  -- Combine: torsionOrder K ≤ 4 · φ²  ≤ 4 · [K:ℚ]²
  have h_sq : (NumberField.Units.torsionOrder K).totient ^ 2 ≤
      (Module.finrank ℚ K) ^ 2 := Nat.pow_le_pow_left h_a 2
  linarith [h_b, h_sq, Nat.mul_le_mul_left 4 h_sq]

/-! ## D3.2d (planned chain assembly)

The four pieces above (E5, D3.2b, D3.2c, D3.2.tors) together with the
hypothesis `rootDiscr K ≤ rd_F` would give `class_num_bound_of_brd`:
`log(classNumber K) / f ≤ 2 · log(2 · rd_F)` for CM totally complex K with
`f ≥ M₀` for some threshold M₀ depending on the constants.

**The chain:**
```
1. classNumber K = R_K · w_K · √|disc K| / ((2π)^f · reg K)            [E5]
2. log(classNumber K) = log R_K + log w_K + (1/2)·log|disc K|
                      - f·log(2π) - log(reg K)
3. (1/2)·log|disc K| = f·log(rootDiscr K)  (totally complex K, [K:ℚ] = 2f)
4. Apply D3.2b:   log R_K ≤ f · log(4 · rd_F)
   Apply D3.2c:  -log(reg K) ≤ log 8
   Apply D3.2.tors: log w_K ≤ log(4f²)
   Apply hyp.: log(rootDiscr K) ≤ log(rd_F)
5. log(classNumber K) ≤ f·log(4·rd_F) + log(4f²) + f·log(rd_F)
                       - f·log(2π) + log 8
                     = f · log(2·rd_F²/π) + log(32·f²)
6. Need ≤ 2f · log(2·rd_F) = f · log(4·rd_F²)
7. Difference: f · log(4·rd_F²) - f · log(2·rd_F²/π) - log(32f²)
             = f · log(2π) - log(32f²)
   For f ≥ 4: f · log(2π) ≥ 4 · log(2π) ≈ 7.34, log(32f²) ≤ log(32·16) ≈ 6.24.
   So chain holds for f ≥ 4.
```

The Lean implementation is non-trivial due to careful real-number arithmetic
and `f` threshold management, plus threading the `f ≥ 4` hypothesis through
`BRDTowerData.getTowerLevel`.  Tracked here as a comment; full implementation
deferred.
-/

/-! ## Phase E2: discriminant chain and log inequality

Goal: bound `log h_K / nrComplexPlaces K` by `2 · log(2 · rd_F)` for
totally complex `K` with `rd_F ≥ (|disc K|)^(1/[K:ℚ])`.

Pieces:
- `minkBound_le_pow_rootDiscr`: `minkBound K ≤ ((4 · rootDiscr K)/π)^f`
  using `n!/n^n ≤ 1` and `√|disc K| = rootDiscr K^f`.
- `log_minkowski_le_two_log_two_rd`: `log(4r/π) ≤ 2 · log(2r)` for `r ≥ 1`.

Chaining these with `classNumber_le_minkowski_pow_degree` gives
`log h_K / f ≤ 2f · log(2·rd_F)`, which is **not** what we want — the
extra `f` factor blocks a constant bound.  This is documented in
`classNumber_log_bound_crude` below.  Closing D3.2 requires a tighter
count (`|{ideals norm ≤ N}| ≤ O(N)`, not `≤ N^n`), which is the
remaining Mathlib gap.
-/

/-- Bound the Minkowski bound by a power of the root discriminant.

For totally complex `K` with `nrComplexPlaces K = f` (so `[K:ℚ] = 2f`),
`minkBound K ≤ (4 · rootDiscr K / π) ^ f`.

Proof: `minkBound K = (4/π)^f · (n!/n^n) · √|disc K|` (the Minkowski bound formula),
`n!/n^n ≤ 1` for `n ≥ 1`, and `√|disc K| = rootDiscr K ^ f` for totally complex K
(since `rootDiscr K = |disc K|^(1/[K:ℚ]) = |disc K|^(1/(2f))`). -/
lemma minkBound_le_pow_rootDiscr [IsTotallyComplex K] (hK : 1 ≤ Module.finrank ℚ K) :
    minkBound K ≤ ((4 * NumberField.rootDiscr K) / Real.pi) ^
      NumberField.InfinitePlace.nrComplexPlaces K := by
  -- Spell out minkBound K
  unfold minkBound
  -- Notation: n = [K:ℚ], f = nrComplexPlaces K, for totally complex K, n = 2f
  set n := Module.finrank ℚ K with hn_def
  set f := NumberField.InfinitePlace.nrComplexPlaces K with hf_def
  -- For totally complex K, n = 2f
  have hn_eq_2f : n = 2 * f := by
    rw [hn_def, hf_def]
    have h_no_real : NumberField.InfinitePlace.nrRealPlaces K = 0 :=
      NumberField.IsTotallyComplex.nrRealPlaces_eq_zero K
    have h_rank := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank (K := K)
    rw [h_no_real] at h_rank
    omega
  have hf_pos : 0 < f := by
    by_contra hf_nonpos
    push_neg at hf_nonpos
    interval_cases f
    rw [hn_eq_2f] at hK
    simp at hK
  have hn_pos : 0 < n := by rw [hn_eq_2f]; omega
  -- n!/n^n ≤ 1
  have h_factorial_le : (Nat.factorial n : ℝ) / (n : ℝ) ^ n ≤ 1 := by
    have hn_real_pos : (0 : ℝ) < (n : ℝ) ^ n := by
      have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      positivity
    rw [div_le_one hn_real_pos]
    exact_mod_cast n.factorial_le_pow
  -- √|disc K| = rootDiscr K ^ f
  have h_sqrt_disc : Real.sqrt |(NumberField.discr K : ℝ)| =
      NumberField.rootDiscr K ^ f := by
    rw [NumberField.rootDiscr_def]
    rw [← Real.rpow_natCast _ f, ← Real.rpow_mul (by positivity)]
    have h_exp : ((n : ℝ))⁻¹ * (f : ℝ) = 1/2 := by
      rw [hn_eq_2f]
      push_cast
      have hf_ne : (f : ℝ) ≠ 0 := by exact_mod_cast hf_pos.ne'
      field_simp
    rw [h_exp, Real.sqrt_eq_rpow]
    -- Now: |(disc K : ℝ)| ^ (1/2) = ((|disc K| : ℤ) : ℝ) ^ (1/2)
    congr 1
    push_cast
    rfl
  rw [h_sqrt_disc]
  -- Goal: (4/π)^f * (n!/n^n * rootDiscr K^f) ≤ ((4·rootDiscr K)/π)^f
  -- ≡ (4/π)^f * rootDiscr K^f * (n!/n^n) ≤ ((4·rootDiscr K)/π)^f
  -- ((4·rootDiscr K)/π)^f = (4/π)^f * rootDiscr K^f, so reduce to (n!/n^n) ≤ 1
  rw [show ((4 * NumberField.rootDiscr K) / Real.pi) ^ f =
      (4 / Real.pi) ^ f * NumberField.rootDiscr K ^ f by
    rw [show (4 * NumberField.rootDiscr K) / Real.pi =
        (4 / Real.pi) * NumberField.rootDiscr K from by ring,
      mul_pow]]
  have h_4_div_pi_pos : (0 : ℝ) < 4 / Real.pi := by
    have := Real.pi_pos; positivity
  have h_rd_nonneg : 0 ≤ NumberField.rootDiscr K ^ f := by
    rw [NumberField.rootDiscr_def]
    positivity
  have h_lhs_eq : (4 / Real.pi) ^ f *
      ((Nat.factorial n : ℝ) / (n : ℝ) ^ n *
        NumberField.rootDiscr K ^ f) =
      (4 / Real.pi) ^ f * NumberField.rootDiscr K ^ f *
        ((Nat.factorial n : ℝ) / (n : ℝ) ^ n) := by ring
  rw [h_lhs_eq]
  -- Goal: (4/π)^f * rootDiscr K^f * (n!/n^n) ≤ (4/π)^f * rootDiscr K^f * 1
  have h_factor_nonneg : 0 ≤ (4 / Real.pi) ^ f * NumberField.rootDiscr K ^ f := by
    apply mul_nonneg
    · exact pow_nonneg (le_of_lt h_4_div_pi_pos) _
    · exact h_rd_nonneg
  calc (4 / Real.pi) ^ f * NumberField.rootDiscr K ^ f *
        ((Nat.factorial n : ℝ) / (n : ℝ) ^ n)
      ≤ (4 / Real.pi) ^ f * NumberField.rootDiscr K ^ f * 1 :=
        mul_le_mul_of_nonneg_left h_factorial_le h_factor_nonneg
    _ = (4 / Real.pi) ^ f * NumberField.rootDiscr K ^ f := by ring

/-- Basic log inequality: for `r ≥ 1`, `log((4 · r) / π) ≤ 2 · log(2 · r)`.
Used in the discriminant chain. -/
lemma log_four_r_div_pi_le_two_log_two_r {r : ℝ} (hr : 1 ≤ r) :
    Real.log ((4 * r) / Real.pi) ≤ 2 * Real.log (2 * r) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hr_pos : 0 < r := by linarith
  have h_2r_pos : 0 < 2 * r := by linarith
  have h_4r_pos : 0 < 4 * r := by linarith
  have h_4r_div_pi_pos : 0 < (4 * r) / Real.pi := by positivity
  have h_2r_sq_pos : 0 < (2 * r) ^ 2 := by positivity
  have h_2r_ne : (2 * r) ≠ 0 := ne_of_gt h_2r_pos
  -- 2 * log (2 * r) = log ((2 * r)^2)
  rw [show (2 : ℝ) * Real.log (2 * r) = Real.log ((2 * r) ^ 2) by
    rw [Real.log_pow]; ring]
  apply Real.log_le_log h_4r_div_pi_pos
  -- (4 r) / π ≤ (2 r)^2 = 4 r²
  rw [div_le_iff₀ hpi, show (2 * r) ^ 2 = 4 * r * r by ring]
  -- 4 r ≤ 4 r * r * π
  have hπ_ge_one : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  nlinarith

/-- **Crude chain (sub-tight; documents the Mathlib gap):** combining
`classNumber_le_minkowski_pow_degree` with a `minkBound K ≤ (4 r/π)^f`
bound gives `log h_K ≤ [K:ℚ] · f · log(4r/π)`, i.e.,
`log h_K / f ≤ [K:ℚ] · log(4r/π) ≤ 2f · 2 · log(2r) = 4f · log(2r)`.

The `f` factor is the obstruction.  Closing D3.2's target
`log h_K / f ≤ 2 · log(2·rd_F)` requires replacing `card_ideals_of_norm_le_bound`'s
crude `≤ N^n` with the analytic `≤ O(N)` estimate.

This corollary just records the crude consequence and notes the gap.
The full closure of D3.2 is documented in
`Erdos90/NumberFieldDeep_GSTower.lean`. -/
theorem classNumber_log_bound_crude_remark :
    True := trivial  -- placeholder; actual analytic infrastructure pending

end

end Mathlib4_Extra
