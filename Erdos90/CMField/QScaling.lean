import Mathlib
import Erdos90.CMField.Basic
import Erdos90.Mathlib4_Extra.FractionalIdealCount

open NumberField FractionalIdeal IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

/-!
# Q²-scaling: integrality of `α / c(α)` after multiplication by Q²

For a CM field `K` with split prime data `sp : SplitPrimeData K m`, this file
proves the key arithmetic lemma underlying the `h_div_conj_mem_Λ` field of
`CMTowerData`: if `α ∈ K^×` satisfies the fractional-ideal equation
`(α)·J(ε₁) = J(ε₂)` and the rational integer `Q` has `count K 𝔓_j (Q) = 1`
at every split prime (and its conjugate), then `Q² · (α / c(α)) ∈ 𝓞_K`.

## Main result

* `Q_sq_div_conj_mem_integers` — the integrality statement above, presented as
  an existence claim `∃ β : 𝓞 K, (β : K) = Q² · (α / c(α))`.

## Proof outline

Set `y := Q² · α / c(α)` and let `v` be a height-one prime of `𝓞_K`.
- **Split case** `v = 𝔓_j`: `count(α) at 𝔓_j = b_j - a_j ∈ {-1,0,1}` (from
  `(α)·J(ε₁) = J(ε₂)` plus `count_J_eq`), `count(c(α)) at 𝔓_j = a_j - b_j`
  (via `count_conj_swap` + `count_J_conj_eq`), giving `count(y) at 𝔓_j =
  2 + 2(b_j - a_j) ∈ {0,2,4} ≥ 0`.
- **Conjugate case** `v = c(𝔓_j)`: symmetric.
- **Other case** `v ∉ split primes`: `count(α) = count(c(α)) = 0` (J's only
  factor at split primes), so `count(y) = 2 · count(Q) ≥ 0` (Q is a rational
  integer, hence its span has nonneg count).

Then `spanSingleton 𝓞⁰ y ≤ 1` via the factorization theorem, so
`y ∈ (1 : FractionalIdeal 𝓞⁰ K)`, i.e., `y ∈ (algebraMap (𝓞 K) K).range`.
-/

namespace Erdos90.CMField

open IsDedekindDomain (HeightOneSpectrum)
open FractionalIdeal

variable {K : Type*} [Field K] [NumberField K] [IsCMField K]

/-- `Q²·α/c(α)` as an element of `K`. -/
private def yval (Q : ℕ) (α : K) : K :=
  ((Q : K))^2 * (α / IsCMField.complexConj K α)

omit [IsCMField K] in
/-- A nonzero principal fractional ideal. -/
private lemma spanSingleton_ne_zero_of_ne_zero {x : K} (hx : x ≠ 0) :
    (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) ≠ 0 := by
  intro h
  rw [FractionalIdeal.spanSingleton_eq_zero_iff] at h
  exact hx h

/-- `Q²·α/c(α)` viewed as a fractional ideal. -/
private lemma spanSingleton_yval_eq {m : ℕ} (sp : SplitPrimeData K m)
    {α : K} (_hα : α ≠ 0) (_hcα : IsCMField.complexConj K α ≠ 0)
    (_hQ_K : ((sp.Q : ℕ) : K) ≠ 0) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (yval sp.Q α) =
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((sp.Q : ℕ) : K))^2 *
        FractionalIdeal.spanSingleton (𝓞 K)⁰ α *
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (IsCMField.complexConj K α))⁻¹ := by
  unfold yval
  rw [div_eq_mul_inv]
  rw [show ((sp.Q : ℕ) : K)^2 * (α * (IsCMField.complexConj K α)⁻¹)
        = ((sp.Q : ℕ) : K)^2 * α * (IsCMField.complexConj K α)⁻¹ from by ring]
  rw [FractionalIdeal.spanSingleton_pow]
  rw [FractionalIdeal.spanSingleton_inv]
  rw [FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]

-- Membership characterizations are now in `Erdos90.Mathlib4_Extra.FractionalIdealCount`.

/-- **Q²-scaling integrality lemma.** Suppose `K` is a CM field with split prime
data `sp : SplitPrimeData K m`. If `α ∈ K^×` satisfies the fractional-ideal
equation `(α) · J(ε₁) = J(ε₂)` and `Q = sp.Q` has count 1 at every split prime
and every conjugate split prime, then `Q² · (α / c(α)) ∈ 𝓞_K`. -/
theorem Q_sq_div_conj_mem_integers {m : ℕ}
    (sp : SplitPrimeData K m)
    (h_Q_count_split : ∀ j : Fin m,
      FractionalIdeal.count K (sp.toHeightOneSpectrum (j := j))
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((sp.Q : ℕ) : K)) = 1)
    (h_Q_count_conj : ∀ j : Fin m,
      FractionalIdeal.count K (sp.conj_toHeightOneSpectrum (j := j))
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((sp.Q : ℕ) : K)) = 1)
    (ε₁ ε₂ : Fin m → Bool) (α : K) (hα : α ≠ 0)
    (hα_eq : FractionalIdeal.spanSingleton (𝓞 K)⁰ α * J_ideal K sp ε₁ =
        J_ideal K sp ε₂) :
    ∃ β : 𝓞 K, (β : K) = ((sp.Q : ℕ) : K)^2 * (α / IsCMField.complexConj K α) := by
  -- Set up notation and basic facts
  have hcα : IsCMField.complexConj K α ≠ 0 := by
    intro h
    apply hα
    have := congrArg (IsCMField.complexConj K) h
    simpa [IsCMField.complexConj_apply_apply K] using this
  have hQ_pos : (0 : ℕ) < sp.Q := sp.h_Q_pos
  have hQ_K_ne_zero : ((sp.Q : ℕ) : K) ≠ 0 := by
    exact_mod_cast hQ_pos.ne'
  have hα_K_ne_zero : (FractionalIdeal.spanSingleton (𝓞 K)⁰ α) ≠ 0 :=
    spanSingleton_ne_zero_of_ne_zero hα
  have hcα_K_ne_zero : (FractionalIdeal.spanSingleton (𝓞 K)⁰ (IsCMField.complexConj K α)) ≠ 0 :=
    spanSingleton_ne_zero_of_ne_zero hcα
  have hQ_K_ne_zero' : (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((sp.Q : ℕ) : K)) ≠ 0 :=
    spanSingleton_ne_zero_of_ne_zero hQ_K_ne_zero
  set y : K := ((sp.Q : ℕ) : K)^2 * (α / IsCMField.complexConj K α) with hy_def
  have hy_ne : y ≠ 0 := by
    rw [hy_def]
    refine mul_ne_zero (pow_ne_zero _ hQ_K_ne_zero) ?_
    exact div_ne_zero hα hcα
  have hy_span_ne : (FractionalIdeal.spanSingleton (𝓞 K)⁰ y) ≠ 0 :=
    spanSingleton_ne_zero_of_ne_zero hy_ne
  -- Step A: count_y_at_v in terms of count of α, c(α), Q at v.
  -- Expand spanSingleton(y) = (Q)^2 · (α) · (cα)⁻¹
  have hyfac : FractionalIdeal.spanSingleton (𝓞 K)⁰ y =
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((sp.Q : ℕ) : K))^2 *
        FractionalIdeal.spanSingleton (𝓞 K)⁰ α *
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (IsCMField.complexConj K α))⁻¹ := by
    have := spanSingleton_yval_eq sp hα hcα hQ_K_ne_zero
    simpa [yval, hy_def] using this
  -- Count expansion lemma
  have hcount_y (v : HeightOneSpectrum (𝓞 K)) :
      count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ y) =
        2 * count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((sp.Q : ℕ) : K)) +
        count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ α) -
        count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (IsCMField.complexConj K α)) := by
    rw [hyfac]
    rw [FractionalIdeal.count_mul K v
        (by exact mul_ne_zero (pow_ne_zero _ hQ_K_ne_zero') hα_K_ne_zero) (inv_ne_zero hcα_K_ne_zero)]
    rw [FractionalIdeal.count_mul K v (pow_ne_zero _ hQ_K_ne_zero') hα_K_ne_zero]
    rw [FractionalIdeal.count_inv]
    have hpow : count K v ((FractionalIdeal.spanSingleton (𝓞 K)⁰ ((sp.Q : ℕ) : K))^2)
        = 2 * count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((sp.Q : ℕ) : K)) := by
      rw [show ((FractionalIdeal.spanSingleton (𝓞 K)⁰ ((sp.Q : ℕ) : K)) : FractionalIdeal _ _)^2
          = (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((sp.Q : ℕ) : K))^(2 : ℕ) from rfl]
      rw [FractionalIdeal.count_pow]
      push_cast; ring
    linarith [hpow]
  -- Step B: count of α at 𝔓_j and at c(𝔓_j), from hα_eq
  -- (α) = (J ε₂) · (J ε₁)⁻¹
  -- count α at v = count (J ε₂) at v - count (J ε₁) at v
  have hcount_α (v : HeightOneSpectrum (𝓞 K)) :
      count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ α) =
        count K v (J_ideal K sp ε₂) - count K v (J_ideal K sp ε₁) := by
    have hJε₁_ne : J_ideal K sp ε₁ ≠ 0 := J_ideal_ne_zero K sp ε₁
    have hJε₂_ne : J_ideal K sp ε₂ ≠ 0 := J_ideal_ne_zero K sp ε₂
    -- From hα_eq: spanSingleton(α) * J(ε₁) = J(ε₂)
    -- So spanSingleton(α) = J(ε₂) * J(ε₁)⁻¹
    have h_α_eq_div : FractionalIdeal.spanSingleton (𝓞 K)⁰ α =
        J_ideal K sp ε₂ * (J_ideal K sp ε₁)⁻¹ := by
      have h := hα_eq
      rw [← h, mul_assoc, mul_inv_cancel₀ hJε₁_ne, mul_one]
    rw [h_α_eq_div, FractionalIdeal.count_mul K v hJε₂_ne (inv_ne_zero hJε₁_ne),
        FractionalIdeal.count_inv]
    ring
  -- Step C: count of c(α) at v = count of α at c(v) (via count_conj_swap)
  have hcount_cα (v : HeightOneSpectrum (𝓞 K)) :
      count K (conjHeightOneSpectrum K v)
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (IsCMField.complexConj K α)) =
      count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ α) := by
    -- count_conj_swap states this for `((complexConj K α : K))` but we need to align coercions
    -- We use the explicit RingOfIntegersComplexConj formulation.
    -- For abstract α : K not necessarily in 𝓞_K, we use count_conj_swap' applied to spanSingleton α.
    have hcount := count_conj_swap' K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ α) hα_K_ne_zero
    -- Rewrite the LHS to match
    rw [FractionalIdeal.ringEquivOfRingEquiv_spanSingleton K K
      ((IsCMField.ringOfIntegersComplexConj K).toRingEquiv) α] at hcount
    -- The image of α under the lifted ring equiv equals complexConj K α
    have h_conj_K : (IsFractionRing.ringEquivOfRingEquiv (A := 𝓞 K) (K := K) (B := 𝓞 K) (L := K)
        ((IsCMField.ringOfIntegersComplexConj K).toRingEquiv)) α = IsCMField.complexConj K α := by
      have h_field_eq : (IsFractionRing.ringEquivOfRingEquiv (A := 𝓞 K) (K := K) (B := 𝓞 K) (L := K)
          (IsCMField.ringOfIntegersComplexConj K).toRingEquiv : K →+* K) =
          (IsCMField.complexConj K : K →+* K) := by
        apply IsFractionRing.ringHom_ext (A := 𝓞 K) (K := K) (L := K)
        intro a
        simp [IsCMField.coe_ringOfIntegersComplexConj K]
      calc (IsFractionRing.ringEquivOfRingEquiv (A := 𝓞 K) (K := K) (B := 𝓞 K) (L := K)
              (IsCMField.ringOfIntegersComplexConj K).toRingEquiv) α
          = (IsFractionRing.ringEquivOfRingEquiv (A := 𝓞 K) (K := K) (B := 𝓞 K) (L := K)
              (IsCMField.ringOfIntegersComplexConj K).toRingEquiv : K →+* K) α := rfl
        _ = (IsCMField.complexConj K : K →+* K) α := by rw [h_field_eq]
        _ = IsCMField.complexConj K α := rfl
    rw [h_conj_K] at hcount
    exact hcount
  -- The full statement we need: count of (complexConj K α) at v = count of α at c(v)
  have hcount_cα_at_v (v : HeightOneSpectrum (𝓞 K)) :
      count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (IsCMField.complexConj K α)) =
      count K (conjHeightOneSpectrum K v)
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ α) := by
    -- Apply hcount_cα to (conjHeightOneSpectrum K v), then use c(c(v)) = v
    have h := hcount_cα (conjHeightOneSpectrum K v)
    -- conjHeightOneSpectrum K (conjHeightOneSpectrum K v) = v
    have hcc : conjHeightOneSpectrum K (conjHeightOneSpectrum K v) = v := by
      apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
      simp [conjHeightOneSpectrum]
    rw [hcc] at h
    exact h
  -- Step D: now reduce the main goal.
  -- We want: ∃ β : 𝓞 K, (β : K) = y
  -- Equivalent to: y ∈ algebraMap range
  suffices h_in_range : y ∈ (algebraMap (𝓞 K) K).range by
    obtain ⟨β, hβ⟩ := h_in_range
    exact ⟨β, hβ⟩
  -- Use the bridge from Mathlib4_Extra: count nonneg everywhere → y in range
  refine Mathlib4_Extra.mem_range_of_spanSingleton_count_nonneg (R := 𝓞 K) (K := K) hy_ne ?_
  intro v
  rw [hcount_y v]
  -- Use Bool→ℤ for the count arithmetic
  -- a_j := (ε₁ j).toNat, b_j := (ε₂ j).toNat
  -- We'll case-split on v's relationship to the split primes
  -- Case analysis: v = sp.toHeightOneSpectrum j, v = sp.conj_toHeightOneSpectrum j, or other
  by_cases hcase : ∃ j : Fin m, v = sp.toHeightOneSpectrum (j := j)
  · -- Case 1: v = 𝔓_j
    obtain ⟨j, hvj⟩ := hcase
    subst hvj
    have hQ : count K (sp.toHeightOneSpectrum (j := j))
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((sp.Q : ℕ) : K)) = 1 := h_Q_count_split j
    rw [hQ]
    -- count α at 𝔓_j = count J(ε₂) - count J(ε₁) at 𝔓_j
    -- count_J_eq: count K v (J_ideal K sp ε) at sp.toHOS j = if ε j then 1 else 0
    have hαv : count K (sp.toHeightOneSpectrum (j := j))
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ α) =
        (if ε₂ j then 1 else 0) - (if ε₁ j then 1 else 0) := by
      rw [hcount_α]
      rw [count_J_eq K sp ε₂ j, count_J_eq K sp ε₁ j]
    -- count cα at 𝔓_j = count α at c(𝔓_j) = count J(ε₂) - count J(ε₁) at c(𝔓_j)
    --                = (if ε₂ j then 0 else 1) - (if ε₁ j then 0 else 1)
    have hcαv : count K (sp.toHeightOneSpectrum (j := j))
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (IsCMField.complexConj K α)) =
        (if ε₂ j then 0 else 1) - (if ε₁ j then 0 else 1) := by
      rw [hcount_cα_at_v]
      -- Need: conjHeightOneSpectrum K (sp.toHOS j) = sp.conj_toHOS j
      have h_conj_eq : conjHeightOneSpectrum K (sp.toHeightOneSpectrum (j := j)) =
          sp.conj_toHeightOneSpectrum (j := j) := by
        apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
        simp [conjHeightOneSpectrum, SplitPrimeData.toHeightOneSpectrum,
              SplitPrimeData.conj_toHeightOneSpectrum]
      rw [h_conj_eq, hcount_α]
      rw [count_J_conj_eq K sp ε₂ j, count_J_conj_eq K sp ε₁ j]
    rw [hαv, hcαv]
    -- 2*1 + (b - a) - ((1-b) - (1-a)) = 2 + 2(b-a)  ∈ {0, 2, 4}
    cases ε₁ j <;> cases ε₂ j <;> simp
  · simp only [not_exists] at hcase
    by_cases hcase2 : ∃ j : Fin m, v = sp.conj_toHeightOneSpectrum (j := j)
    · -- Case 2: v = c(𝔓_j)
      obtain ⟨j, hvj⟩ := hcase2
      subst hvj
      have hQ : count K (sp.conj_toHeightOneSpectrum (j := j))
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((sp.Q : ℕ) : K)) = 1 := h_Q_count_conj j
      rw [hQ]
      have hαv : count K (sp.conj_toHeightOneSpectrum (j := j))
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ α) =
          (if ε₂ j then 0 else 1) - (if ε₁ j then 0 else 1) := by
        rw [hcount_α]
        rw [count_J_conj_eq K sp ε₂ j, count_J_conj_eq K sp ε₁ j]
      have hcαv : count K (sp.conj_toHeightOneSpectrum (j := j))
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ (IsCMField.complexConj K α)) =
          (if ε₂ j then 1 else 0) - (if ε₁ j then 1 else 0) := by
        rw [hcount_cα_at_v]
        -- conjHeightOneSpectrum K (sp.conj_toHOS j) = sp.toHOS j
        have h_conj_eq : conjHeightOneSpectrum K (sp.conj_toHeightOneSpectrum (j := j)) =
            sp.toHeightOneSpectrum (j := j) := by
          apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
          simp [conjHeightOneSpectrum, SplitPrimeData.toHeightOneSpectrum,
                SplitPrimeData.conj_toHeightOneSpectrum, conjIdeal_conjIdeal]
        rw [h_conj_eq, hcount_α]
        rw [count_J_eq K sp ε₂ j, count_J_eq K sp ε₁ j]
      rw [hαv, hcαv]
      cases ε₁ j <;> cases ε₂ j <;> simp
    · simp only [not_exists] at hcase2
      -- Case 3: v is not any 𝔓_j nor any c(𝔓_j)
      -- Need: count of α and c(α) at v are both 0; count of Q at v ≥ 0.
      -- The "other" case requires also that c(v) is "other", which holds via the
      -- pairing: if v ∉ split primes, c(v) ∉ split primes (otherwise v = c(c(v)) ∈ split-pair).
      -- count(J ε) at v = 0 for any v ∉ split primes (use count_prod + count_maximal_coprime).
      have hcount_J_zero (ε : Fin m → Bool) : count K v (J_ideal K sp ε) = 0 := by
        dsimp [J_ideal]
        have hS : ∀ (j : Fin m),
            (if ε j then (sp.primes j : FractionalIdeal (𝓞 K)⁰ K)
             else (conjIdeal K (sp.primes j) : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 := by
          intro j
          split
          · exact FractionalIdeal.coeIdeal_ne_zero.mpr (sp.h_ne_bot j)
          · exact FractionalIdeal.coeIdeal_ne_zero.mpr (conjIdeal_ne_bot K (sp.h_ne_bot j))
        rw [FractionalIdeal.count_prod K v (Finset.univ : Finset (Fin m)) _ (fun j _ => hS j)]
        apply Finset.sum_eq_zero
        intro j _
        split
        · -- ε j = true: factor is (sp.primes j) — corresponds to sp.toHOS j
          have h_factor_eq : (sp.primes j : FractionalIdeal (𝓞 K)⁰ K) =
              ((sp.toHeightOneSpectrum (j := j)).asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
            simp [SplitPrimeData.toHeightOneSpectrum]
          rw [h_factor_eq]
          exact FractionalIdeal.count_maximal_coprime K v (Ne.symm (hcase j))
        · -- ε j = false: factor is c(sp.primes j) — corresponds to sp.conj_toHOS j
          have h_factor_eq : (conjIdeal K (sp.primes j) : FractionalIdeal (𝓞 K)⁰ K) =
              ((sp.conj_toHeightOneSpectrum (j := j)).asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
            simp [SplitPrimeData.conj_toHeightOneSpectrum]
          rw [h_factor_eq]
          exact FractionalIdeal.count_maximal_coprime K v (Ne.symm (hcase2 j))
      have hαv0 : count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ α) = 0 := by
        rw [hcount_α v]
        rw [hcount_J_zero ε₂, hcount_J_zero ε₁]
        ring
      -- For count(c α) at v: also need it to be 0.
      -- c(α) at v = count(α) at c(v). And c(v) is also "other" by the pairing argument.
      have hcv_other_split : ∀ j, conjHeightOneSpectrum K v ≠ sp.toHeightOneSpectrum (j := j) := by
        intro j h
        apply hcase2 j
        apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
        have h_ideal : conjIdeal K v.asIdeal = sp.primes j := by
          simpa [conjHeightOneSpectrum, SplitPrimeData.toHeightOneSpectrum] using
            congrArg (fun x => x.asIdeal) h
        have hv_eq : v.asIdeal = conjIdeal K (sp.primes j) := by
          have hcc := congrArg (conjIdeal K) h_ideal
          rw [conjIdeal_conjIdeal] at hcc
          exact hcc
        rw [hv_eq]
        simp [SplitPrimeData.conj_toHeightOneSpectrum]
      have hcv_other_conj : ∀ j, conjHeightOneSpectrum K v ≠ sp.conj_toHeightOneSpectrum (j := j) := by
        intro j h
        apply hcase j
        apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
        have h_ideal : conjIdeal K v.asIdeal = conjIdeal K (sp.primes j) := by
          simpa [conjHeightOneSpectrum, SplitPrimeData.conj_toHeightOneSpectrum] using
            congrArg (fun x => x.asIdeal) h
        have hv_eq : v.asIdeal = sp.primes j := conjIdeal_injective K h_ideal
        rw [hv_eq]
        simp [SplitPrimeData.toHeightOneSpectrum]
      -- count(α) at c(v) = 0 by the same argument (other case applied to c(v))
      have hcount_J_zero_at_cv (ε : Fin m → Bool) :
          count K (conjHeightOneSpectrum K v) (J_ideal K sp ε) = 0 := by
        dsimp [J_ideal]
        have hS : ∀ (j : Fin m),
            (if ε j then (sp.primes j : FractionalIdeal (𝓞 K)⁰ K)
             else (conjIdeal K (sp.primes j) : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 := by
          intro j
          split
          · exact FractionalIdeal.coeIdeal_ne_zero.mpr (sp.h_ne_bot j)
          · exact FractionalIdeal.coeIdeal_ne_zero.mpr (conjIdeal_ne_bot K (sp.h_ne_bot j))
        rw [FractionalIdeal.count_prod K (conjHeightOneSpectrum K v)
              (Finset.univ : Finset (Fin m)) _ (fun j _ => hS j)]
        apply Finset.sum_eq_zero
        intro j _
        split
        · have h_factor_eq : (sp.primes j : FractionalIdeal (𝓞 K)⁰ K) =
              ((sp.toHeightOneSpectrum (j := j)).asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
            simp [SplitPrimeData.toHeightOneSpectrum]
          rw [h_factor_eq]
          exact FractionalIdeal.count_maximal_coprime K (conjHeightOneSpectrum K v)
            (Ne.symm (hcv_other_split j))
        · have h_factor_eq : (conjIdeal K (sp.primes j) : FractionalIdeal (𝓞 K)⁰ K) =
              ((sp.conj_toHeightOneSpectrum (j := j)).asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
            simp [SplitPrimeData.conj_toHeightOneSpectrum]
          rw [h_factor_eq]
          exact FractionalIdeal.count_maximal_coprime K (conjHeightOneSpectrum K v)
            (Ne.symm (hcv_other_conj j))
      have hcαv0 : count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (IsCMField.complexConj K α))
          = 0 := by
        rw [hcount_cα_at_v]
        rw [hcount_α]
        rw [hcount_J_zero_at_cv ε₂, hcount_J_zero_at_cv ε₁]
        ring
      -- count(Q) at v ≥ 0: span Q is the image of a positive integer ideal
      have hQ_int : count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((sp.Q : ℕ) : K)) ≥ 0 := by
        have h_eq : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((sp.Q : ℕ) : K) =
            ((Ideal.span {((sp.Q : ℕ) : 𝓞 K)} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
          rw [FractionalIdeal.coeIdeal_span_singleton]
          simp
        rw [h_eq]
        exact FractionalIdeal.count_coe_nonneg K v _
      rw [hαv0, hcαv0]
      linarith

end Erdos90.CMField

end
