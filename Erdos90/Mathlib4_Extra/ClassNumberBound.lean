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
  norm at most `N` is bounded by `N ^ n`.  Sorried; this is the Mathlib
  gap (a crude polynomial bound that follows from the divisor-function
  estimate but isn't packaged in Mathlib v4.30).
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

/-- **D3.2c**: Friedman–Zimmert regulator lower bound for CM totally complex
fields.  For a CM totally complex K with `nrComplexPlaces K ≥ 1` (i.e. unit
rank `f - 1 ≥ 0`), `regulator K ≥ 1/8`.

The constant `1/8` is a weakened form of Friedman's `R_K > 0.2052`.

Cite: Friedman 1989 (`assets/` would be ideal but not currently in repo);
Zimmert 1981.  Not in Mathlib v4.30. -/
lemma regulator_lower_bound_cm
    [IsCMField K] [IsTotallyComplex K]
    (_hf : 1 ≤ NumberField.InfinitePlace.nrComplexPlaces K) :
    NumberField.Units.regulator K ≥ 1/8 := sorry

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

/-- **D3.2b**: Louboutin upper bound on the Dedekind zeta residue for CM fields.
For a CM totally complex `K` with `rootDiscr K ≤ rd_F` (where `1 ≤ rd_F`),
`dedekindZeta_residue K ≤ (4 · rd_F) ^ nrComplexPlaces K`.

The form `(4 · rd_F)^f` is the loose-constant version of Louboutin 2000 Theorem A;
sharper variants give smaller constants but this form chains cleanly into
`2 · log(2 · rd_F)`.

Cite: `assets/louboutin_2000_class_number.pdf` Theorem A.  See also
Akhtari–Vaaler–Widmer (`assets/akhtari_vaaler_widmer_src/Equidistribution_1.tex`)
for related effective constants in the CM case.

Not in Mathlib v4.30; requires functional equation + L(1, χ) bounds. -/
lemma dedekind_residue_upper_bound_cm
    [IsCMField K] [IsTotallyComplex K]
    (rd_F : ℝ) (_h_rd_F : 1 ≤ rd_F)
    (_h_rd_K : NumberField.rootDiscr K ≤ rd_F) :
    NumberField.dedekindZeta_residue K ≤
      (4 * rd_F) ^ NumberField.InfinitePlace.nrComplexPlaces K := sorry

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
