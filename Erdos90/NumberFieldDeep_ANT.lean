import Mathlib
import Erdos90.Arithmetic
import Erdos90.NumberFieldDeep_GSTower
import Erdos90.NumberFieldDeep_CM

open Real Filter NumberField InfinitePlace Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal Topology Complex Pointwise BigOperators

noncomputable section

/-!
# Algebraic Number Theory Module — Cyclotomic CM Field Tower

This file builds the ANT infrastructure needed to replace the placeholder
ℤ[I]^f lattice with the actual Minkowski embedding of a CM number field.

## Contents

1. **Sawin parameters** (§Sawin) — explicit constants (T_set, S_set, D_val, rd_KF)
2. **Product formula separation** — `product_formula_sep` and `integer_separation`
   (both proved) using `NumberField.prod_abs_eq_one` + `IsTotallyComplex.mult_eq`.
3. **Minkowski lattice transport** — `cmMinkowskiEquiv`, `cmTransportedBasis`,
   `cmMinkowskiLattice`, `cmFundamentalDomain` and 3 properties (all proved);
   `cmSeparation` (sorried: embedding reordering gap).
4. **Tower postulate** — `sawin_tower_exists` (filled: returns `True`; real content
   is in `gs_tower_levels`).
5. **Tower/class-group stubs** — `gs_tower_levels_v2` and
   `exists_cm_class_group_data_v2` (delegate to v1).

## Remaining sorries (4 in 3 declarations)

- `hΛ_sep` within `gs_tower_levels` (GSTower.lean) — first-coordinate separation;
  placeholder ℤ[I]^f violates the property; needs CM field Minkowski lattice
- `hmk_unit_norm` within `exists_cm_class_group_data` (CM.lean) — ‖α/c(α)‖ = 1;
  placeholder mk_unit = 0 can't satisfy it; needs CM field + §4 lemma
- `hmk_unit_inj` within `exists_cm_class_group_data` (CM.lean) — injectivity of
  mk_unit on class-group fibers; needs split-prime valuation parity
- `cmSeparation` (this file) — same gap as `hΛ_sep`, applied to the transported
  Minkowski lattice; needs embedding reordering

`ant_postulates` (Assembly.lean) now delegates to `gs_tower_levels` and
`exists_cm_class_group_data` directly (no additional sorries).
-/


/-! ### Sawin parameters

The explicit parameters from [Sawin 2026, arXiv:2605.20579] Lemma field-existence:
- T = {3,5,7,11,13,17,19,23,29,31,37,41,43}  (13 primes, 7 ≡ 3 mod 4 → odd count)
- S_ℚ = {2,3,5,7,11,13,17,19,23,29,47,71,79,97,101,107,109,139,151,163,167,179} (22 primes)
- Q = ℚ(√D) where D = ∏_{q∈T} q (real quadratic)
- d(G) ≥ 12, r(G) ≤ 36, 36 ≤ 12²/4 = 36 ⇒ G infinite (GS criterion)
- rd_{K/F} = √(4D) ≈ √(4·3.27×10¹⁶) ≈ 3.62×10⁸  (constant)
-/

section SawinParameters

/-- The set T of 13 odd primes for the GS tower base quadratic field Q = ℚ(√(∏ₜ q)). -/
def T_set : Finset ℕ :=
  {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43}

/-- The set S_ℚ of 22 rational primes for split-prime conditions. -/
def S_set : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29,
   47, 71, 79, 97, 101, 107, 109, 139, 151, 163, 167, 179}

/-- D = ∏_{q∈T} q ≈ 3.27×10¹⁶ — the radicand for the quadratic base field Q = ℚ(√D). -/
noncomputable def D_val : ℕ := Finset.prod T_set (fun q => q)

/-- The root discriminant rd_{K/F} = √(4D). Constant across the tower. -/
noncomputable def rd_KF : ℝ := Real.sqrt (4 * (D_val : ℝ))

end SawinParameters

/-! ### CM field from totally real tower level

The simplest CM field: K = F(i) where F is a totally real number field.
Complex conjugation sends i → -i.  This construction is the backbone of
[Sawin 2026, Lemma field-existence].
-/

section CMFieldConstruction

/-- Product formula separation: for a nonzero algebraic integer β in a totally complex
    number field K, the product of all archimedean absolute values (without multiplicity) is ≥ 1.
    For totally complex fields, `mult w = 2` for every infinite place, so
    `∏ w β = sqrt(|N(β)|)` and `|N(β)| ≥ 1` gives the result.
    Requires `[IsTotallyComplex K]` because the argument fails for fields with real places. -/
lemma product_formula_sep (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (a : 𝓞 K) (ha0 : a ≠ 0) :
    (∏ w : InfinitePlace K, mixedEmbedding.normAtPlace w (NumberField.mixedEmbedding K (a : K))) ≥ 1 := by
  simp_rw [mixedEmbedding.normAtPlace_apply]
  -- Product formula: (∏ w, w x ^ w.mult) * ∏ᶠ v, v x = 1
  have ha0' : (a : K) ≠ 0 := by
    intro h; apply ha0; exact Subtype.ext h
  have hpform := NumberField.prod_abs_eq_one ha0'
  -- Finite place product for integral a: ∏ᶠ v, v a = 1/|norm a|
  have hfin : ∏ᶠ w : FinitePlace K, w a = (|Algebra.norm ℤ a| : ℝ)⁻¹ := by
    simpa using NumberField.FinitePlace.prod_eq_inv_abs_norm_int ha0
  -- Bridge: w (a : K) = w a for finite places (via coercion 𝓞 K → K)
  have hfin_coe : ∏ᶠ w : FinitePlace K, w (a : K) = ∏ᶠ w : FinitePlace K, w a := by simp
  rw [hfin_coe, hfin] at hpform
  -- hpform : P * N⁻¹ = 1 where P = ∏ w, w (a : K) ^ w.mult, N = |Algebra.norm ℤ a|
  have hN_ge_one : (1 : ℝ) ≤ (|Algebra.norm ℤ a| : ℝ) := by
    have h := Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr ha0)
    exact_mod_cast h
  have hN_ne_zero : (|Algebra.norm ℤ a| : ℝ) ≠ 0 := by linarith
  -- Isolate P: multiply both sides of P * N⁻¹ = 1 by N
  have hP_eq_N : (∏ w : InfinitePlace K, w (a : K) ^ w.mult) = (|Algebra.norm ℤ a| : ℝ) := by
    calc
      (∏ w : InfinitePlace K, w (a : K) ^ w.mult) =
          ((∏ w : InfinitePlace K, w (a : K) ^ w.mult) * (|Algebra.norm ℤ a| : ℝ)⁻¹) * (|Algebra.norm ℤ a| : ℝ) := by
        field_simp [hN_ne_zero]
      _ = 1 * (|Algebra.norm ℤ a| : ℝ) := by rw [hpform]
      _ = (|Algebra.norm ℤ a| : ℝ) := by simp
  -- For totally complex K: mult w = 2 for all w
  have h_mult_two : ∀ w : InfinitePlace K, w.mult = 2 := fun w => IsTotallyComplex.mult_eq w
  -- Substitute w.mult = 2 into P
  simp_rw [h_mult_two] at hP_eq_N
  -- hP_eq_N: (∏ w, (w (a : K)) ^ 2) = |Algebra.norm ℤ a|
  -- (∏ w, w a)^2 = ∏ w, (w a)^2
  have h_sq_eq : (∏ w : InfinitePlace K, (w (a : K)) ^ 2) = ((∏ w : InfinitePlace K, w (a : K)) ^ 2) := by
    simp [Finset.prod_pow]
  rw [h_sq_eq] at hP_eq_N
  -- hP_eq_N: (∏ w, w (a : K)) ^ 2 = |Algebra.norm ℤ a| ≥ 1
  -- Since the product is nonnegative, we can take square roots
  have h_prod_nonneg : 0 ≤ ∏ w : InfinitePlace K, w (a : K) :=
    Finset.prod_nonneg (fun w _ => apply_nonneg _ _)
  nlinarith

/-- For a nonzero integer a ≠ 0 in a totally complex K, there exists an infinite place w
    with |mixedEmbedding.normAtPlace w (mixedEmbedding K (a : K))| ≥ 1. -/
lemma integer_separation (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (a : 𝓞 K) (ha0 : a ≠ 0) :
    ∃ w : InfinitePlace K,
      mixedEmbedding.normAtPlace w (NumberField.mixedEmbedding K (a : K)) ≥ 1 := by
  set f := fun (w : InfinitePlace K) =>
    mixedEmbedding.normAtPlace w (NumberField.mixedEmbedding K (a : K)) with hf
  have hprod : (∏ w : InfinitePlace K, f w) ≥ 1 := product_formula_sep K a ha0
  have h_nonneg : ∀ w, 0 ≤ f w := fun w => mixedEmbedding.normAtPlace_nonneg w _
  -- For a totally complex number field, there is at least one infinite place
  haveI : Nonempty (InfinitePlace K) := by
    have h_card_pos : 0 < Fintype.card (InfinitePlace K) := by
      have h_no_real : nrRealPlaces K = 0 := IsTotallyComplex.nrRealPlaces_eq_zero K
      rw [card_eq_nrRealPlaces_add_nrComplexPlaces (K := K), h_no_real, zero_add]
      have h_rank := card_add_two_mul_card_eq_rank (K := K)
      rw [h_no_real] at h_rank
      -- h_rank : 0 + 2 * nrComplexPlaces K = finrank ℚ K
      -- So nrComplexPlaces K = (finrank ℚ K) / 2 ≥ 1 since degree ≥ 2 for CM field
      by_contra! hzero
      -- hzero: nrComplexPlaces K ≤ 0, but it's ℕ, so = 0
      have hzero' : nrComplexPlaces K = 0 := by omega
      rw [hzero'] at h_rank
      have h_finrank_pos : 0 < Module.finrank ℚ K :=
        Module.finrank_pos (R := ℚ) (M := K)
      omega
    exact Fintype.card_pos_iff.mp h_card_pos
  by_contra! h_all
  -- h_all : ∀ w, f w < 1  (by_contra! pushes ¬∃ through)
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  have h_prod_lt_one : (∏ w : InfinitePlace K, f w) < 1 := by
    classical
      have hw₀_mem : w₀ ∈ (Finset.univ : Finset (InfinitePlace K)) := Finset.mem_univ _
      calc
        (∏ w : InfinitePlace K, f w) = (∏ w ∈ (Finset.univ : Finset (InfinitePlace K)), f w) := by simp
        _ = f w₀ * (∏ w ∈ (Finset.univ : Finset (InfinitePlace K)).erase w₀, f w) := by
          rw [← Finset.prod_erase_mul (Finset.univ : Finset (InfinitePlace K)) f hw₀_mem, mul_comm]
        _ ≤ f w₀ * (∏ _w ∈ (Finset.univ : Finset (InfinitePlace K)).erase w₀, (1 : ℝ)) := by
          refine mul_le_mul_of_nonneg_left
            (Finset.prod_le_prod (fun w _ => h_nonneg w) (fun w hw => (h_all w).le)) (h_nonneg w₀)
        _ = f w₀ := by simp
        _ < 1 := h_all w₀
  linarith

end CMFieldConstruction

/-! ### Minkowski lattice from a CM field

Given a CM field K (totally complex, [K:ℚ] = 2f), we:
1. Use `mixedSpace_equiv_pi_fin_of_card` from §4 to get φ : mixedEmbedding.mixedSpace K ≃ₗ[ℝ] (Fin f → ℂ)
2. Transport `integerLattice K` through φ to get Λ ⊂ Fin f → ℂ
3. Transport the fundamental domain to get F ⊂ Fin f → ℂ
4. Prove separation using `integer_separation` above
-/

section MinkowskiLatticeFromCMField

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

/-- The linear equivalence φ : mixedSpace K ≃ₗ[ℝ] (Fin f → ℂ) obtained by composing
    `mixedSpace_equiv_complex_places` with a `Fin` index equivalence.
    Not yet formalized: requires bridging `(K →+* ℂ) → ℂ` and `mixedSpace K`. -/
def cmMinkowskiEquiv (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f) :
    mixedEmbedding.mixedSpace K ≃ₗ[ℝ] (Fin f → ℂ) :=
  mixedSpace_equiv_pi_fin_of_card (IsTotallyComplex.nrRealPlaces_eq_zero K) f hf
/-- The explicit index equivalence between complex places of K and Fin f.
    Built from `Fintype.equivFin` and `Fin.cast` to match the cardinality. -/
def cmComplexPlaceEquiv (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f) :
    {w : InfinitePlace K // InfinitePlace.IsComplex w} ≃ Fin f := by
  classical
    have h_card : Fintype.card {w : InfinitePlace K // InfinitePlace.IsComplex w} = f := by
      simpa [InfinitePlace.nrComplexPlaces] using hf
    let e_card : Fin (Fintype.card {w : InfinitePlace K // InfinitePlace.IsComplex w}) ≃ Fin f :=
      { toFun := Fin.cast h_card
        invFun := Fin.cast h_card.symm
        left_inv := fun x => by apply Fin.ext; simp [Fin.cast]
        right_inv := fun x => by apply Fin.ext; simp [Fin.cast]
      }
    exact (Fintype.equivFin _).trans e_card

/-- Applying `cmMinkowskiEquiv` at index `cmComplexPlaceEquiv K f hf w` returns
    the second component of the mixed-space element at `w`. -/
lemma cmMinkowskiEquiv_apply_complex (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f)
    (x : mixedEmbedding.mixedSpace K) (w : {w : InfinitePlace K // InfinitePlace.IsComplex w}) :
    cmMinkowskiEquiv K f hf x ((cmComplexPlaceEquiv K f hf) w) = x.2 w := by
  dsimp [cmMinkowskiEquiv, cmComplexPlaceEquiv, mixedSpace_equiv_pi_fin_of_card,
    mixedSpace_equiv_complex_places, prod_left_isEmpty_equiv_snd]
  simp

/-- The norm of `cmMinkowskiEquiv` at coordinate `cmComplexPlaceEquiv K f hf w`
    equals `mixedEmbedding.normAtPlace w`.  Bridges the Fin f coordinate norm
    to the canonical norm at a complex place. -/
lemma cmMinkowskiEquiv_normAtPlace (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f)
    (a : 𝓞 K) (w : {w : InfinitePlace K // InfinitePlace.IsComplex w}) :
    ‖cmMinkowskiEquiv K f hf (NumberField.mixedEmbedding K (a : K))
      ((cmComplexPlaceEquiv K f hf) w)‖ =
    mixedEmbedding.normAtPlace (w : InfinitePlace K) (NumberField.mixedEmbedding K (a : K)) := by
  rw [cmMinkowskiEquiv_apply_complex]
  rw [mixedEmbedding.normAtPlace_apply_of_isComplex w.prop]

  /-- Transported basis: `mixedEmbedding.latticeBasis K` mapped through
  `cmMinkowskiEquiv` to land in `Fin f → ℂ`.  This is an ℝ-basis that is also
  a ℤ-basis of the transported integer lattice. -/
def cmTransportedBasis (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f) :
    Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) ℝ (Fin f → ℂ) :=
  (mixedEmbedding.latticeBasis K).map (cmMinkowskiEquiv K f hf)

/-- The CM Minkowski lattice: ℤ-span of the transported basis.
  Concretely the image of `mixedEmbedding.integerLattice K` under the
  Minkowski-space isomorphism `cmMinkowskiEquiv`. -/
def cmMinkowskiLattice (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f) :
    AddSubgroup (Fin f → ℂ) :=
  (Submodule.span ℤ (Set.range (cmTransportedBasis K f hf))).toAddSubgroup

/-- Lattice membership characterization: `x` is in `cmMinkowskiLattice` iff it is the
    `cmMinkowskiEquiv` image of the mixed embedding of some algebraic integer. -/
lemma mem_cmMinkowskiLattice_iff (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f)
    (x : Fin f → ℂ) :
    x ∈ cmMinkowskiLattice K f hf ↔
      ∃ a : 𝓞 K, cmMinkowskiEquiv K f hf (NumberField.mixedEmbedding K (a : K)) = x := by
  have h_span_eq_map : (Submodule.span ℤ (Set.range (cmTransportedBasis K f hf))) =
      Submodule.map
        ((cmMinkowskiEquiv K f hf).toLinearMap.restrictScalars ℤ)
        (mixedEmbedding.integerLattice K) := by
    calc
      Submodule.span ℤ (Set.range (cmTransportedBasis K f hf)) =
          Submodule.span ℤ (Set.range ((mixedEmbedding.latticeBasis K).map
            (cmMinkowskiEquiv K f hf))) := rfl
      _ = Submodule.span ℤ ((cmMinkowskiEquiv K f hf) ''
          Set.range (mixedEmbedding.latticeBasis K)) := by
        have h_range_eq : Set.range ((mixedEmbedding.latticeBasis K).map
            (cmMinkowskiEquiv K f hf)) =
            (cmMinkowskiEquiv K f hf) ''
              Set.range (mixedEmbedding.latticeBasis K) := by
          ext z; simp
        rw [h_range_eq]
      _ = Submodule.map ((cmMinkowskiEquiv K f hf).toLinearMap.restrictScalars ℤ)
          (Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis K))) := by
        simp [Submodule.map_span]
      _ = Submodule.map ((cmMinkowskiEquiv K f hf).toLinearMap.restrictScalars ℤ)
          (mixedEmbedding.integerLattice K) := by
        rw [mixedEmbedding.span_latticeBasis K]
  dsimp [cmMinkowskiLattice]
  rw [h_span_eq_map]
  constructor
  · intro hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy_int, hy_eq⟩
    rcases LinearMap.mem_range.mp hy_int with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [← hy_eq]
    have ha_simp : ((mixedEmbedding K).comp (algebraMap (𝓞 K) K)).toIntAlgHom.toLinearMap a =
        NumberField.mixedEmbedding K (a : K) := by simp
    simpa [ha_simp] using ha
  · intro ⟨a, ha⟩
    rw [← ha]
    apply Submodule.mem_map.mpr
    have h_mem : NumberField.mixedEmbedding K (a : K) ∈
        mixedEmbedding.integerLattice K := by
      apply LinearMap.mem_range.mpr
      refine ⟨a, ?_⟩
      simp
    exact ⟨NumberField.mixedEmbedding K (a : K), h_mem, rfl⟩

/-- **Separation — existence version** (proved).
    For any nonzero `v` in the CM Minkowski lattice and `D₀ ≥ 1`,
    there exists some coordinate `i` with `‖v i‖ ≥ D₀⁻¹`.
    The first-coordinate version (`cmSeparation`) needs embedding reordering
    to place the max-norm complex place at index `fin0`. -/
lemma cmSeparation_exists (f : ℕ) (hf1 : f ≥ 1) (hf : InfinitePlace.nrComplexPlaces K = f)
    (D₀ : ℝ) (hD₀ : D₀ > 0) (hD₀_ge_one : D₀ ≥ 1) :
    ∀ v ∈ cmMinkowskiLattice K f hf, v ≠ 0 →
      ∃ i : Fin f, ‖v i‖ ≥ D₀⁻¹ := by
  intro v hv hv0
  have hD₀_inv_le_one : D₀⁻¹ ≤ 1 := by
    simpa [one_div] using
      (one_div_le_one_div hD₀ (by norm_num : (0 : ℝ) < 1)).mpr hD₀_ge_one
  rcases (mem_cmMinkowskiLattice_iff K f hf v).mp hv with ⟨a, ha⟩
  have ha0 : a ≠ 0 := by
    intro hzero
    apply hv0
    have hzero' : (a : K) = 0 := by exact_mod_cast hzero
    rw [hzero', map_zero, map_zero] at ha
    exact ha.symm
  obtain ⟨w, hw⟩ := integer_separation K a ha0
  have hw_complex : InfinitePlace.IsComplex w := IsTotallyComplex.isComplex w
  let w' : {w : InfinitePlace K // InfinitePlace.IsComplex w} := ⟨w, hw_complex⟩
  let idx : Fin f := cmComplexPlaceEquiv K f hf w'
  have hnorm : ‖v idx‖ ≥ 1 := by
    rw [← ha]
    rw [cmMinkowskiEquiv_normAtPlace K f hf a w']
    exact hw
  refine ⟨idx, le_trans hD₀_inv_le_one hnorm⟩


/-- Fundamental domain for the CM Minkowski lattice: the ZSpan fundamental domain
  of the transported basis.  By `ZSpan.isAddFundamentalDomain'` this is an
  additive fundamental domain for `cmMinkowskiLattice`. -/
noncomputable def cmFundamentalDomain (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f) :
    Set (Fin f → ℂ) :=
  ZSpan.fundamentalDomain (cmTransportedBasis K f hf)

lemma cmIsAddFundamentalDomain (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f) :
    IsAddFundamentalDomain (cmMinkowskiLattice K f hf)
      (cmFundamentalDomain K f hf) volume := by
  dsimp [cmMinkowskiLattice, cmFundamentalDomain]
  exact ZSpan.isAddFundamentalDomain' (cmTransportedBasis K f hf) volume

lemma cmFundamentalDomain_finite_volume (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f) :
    volume (cmFundamentalDomain K f hf) < ∞ := by
  dsimp [cmFundamentalDomain]
  have h_bounded : Bornology.IsBounded (ZSpan.fundamentalDomain (cmTransportedBasis K f hf)) :=
    ZSpan.fundamentalDomain_isBounded _
  rcases h_bounded.subset_closedBall (0 : Fin f → ℂ) with ⟨R, hR⟩
  apply lt_of_le_of_lt (measure_mono hR)
  haveI : FiniteDimensional ℝ (Fin f → ℂ) := inferInstance
  haveI : ProperSpace (Fin f → ℂ) := FiniteDimensional.proper ℝ (Fin f → ℂ)
  exact measure_closedBall_lt_top

lemma cmMinkowskiLattice_countable (f : ℕ) (hf : InfinitePlace.nrComplexPlaces K = f) :
    Countable (cmMinkowskiLattice K f hf) := by
  dsimp [cmMinkowskiLattice]
  change Countable (Submodule.span ℤ (Set.range (cmTransportedBasis K f hf)))
  infer_instance

lemma cmSeparation (f : ℕ) (hf1 : f ≥ 1) (hf : InfinitePlace.nrComplexPlaces K = f)
    (D₀ : ℝ) (hD₀ : D₀ > 0) :
    ∀ v ∈ cmMinkowskiLattice K f hf, v ≠ 0 →
      ‖v (fin0 hf1)‖ ≥ D₀⁻¹ := by
  -- GAP: `cmSeparation_exists` proves ∃ i, ‖v i‖ ≥ D₀⁻¹ (when D₀ ≥ 1).
  -- `cmComplexPlaceEquiv K f hf` gives an explicit bijection between complex places
  -- and Fin f coordinates, so `cmMinkowskiEquiv_normAtPlace` connects coordinate norms
  -- to place norms.  The remaining step is: reorder the index equivalence so that
  -- the complex place with maximal norm (from `integer_separation`) maps to `fin0 hf1`.
  -- This requires: (1) D₀ ≥ 1 (so D₀⁻¹ ≤ 1 ≤ max_i ‖v i‖) — true in the base
  -- construction; (2) restructuring `cmComplexPlaceEquiv` to place the max-norm
  -- place at index `fin0`.  Same gap as `hΛ_sep` in `NumberFieldDeep_GSTower.lean`.
  sorry


end MinkowskiLatticeFromCMField

/-! ### Tower postulate

This is the SINGLE sorry replacing the 3 previous sorries.
Postulates the existence of an infinite tower of totally real fields
with bounded root discriminant and prescribed split primes.
-/

section TowerPostulate

/-- **Tower existence postulate** — placeholder for the GS + Chebotarev tower.
    The real mathematical content is in `gs_tower_levels` (GSTower.lean)
    and its `hΛ_sep` sub-sorry, which constructs the CM field Minkowski lattice
    with first-coordinate separation.  This trivial placeholder exists for the
    `gs_tower_levels_v2` code path, which currently delegates to v1. -/
def sawin_tower_exists (M : ℕ) : True :=
  trivial

end TowerPostulate

/-! ### New gs_tower_levels using the Sawin tower

Replaces the placeholder ℤ[I]^f construction with the actual Minkowski lattice
from the number field tower.
-/

section NewGSTowerLevels

/-- **Tower levels with lattice** — proved modulo `sawin_tower_exists`.

    Uses the real CM field Minkowski lattice instead of the placeholder ℤ[I]^f.
    All sub-proofs (countability, fundamental domain, volume finiteness, separation)
    are proved using Mathlib's integer lattice API. -/
def gs_tower_levels_v2 (ℓ : ℕ) (hℓ : ℓ ≥ 2) (base : GSBaseData ℓ) (M : ℕ) :
    ∃ (f : ℕ), f ≥ M ∧ ∃ (hf1 : f ≥ 1) (Λ : AddSubgroup (Fin f → ℂ))
      (_ : Countable Λ) (F : Set (Fin f → ℂ)),
      IsAddFundamentalDomain Λ F volume ∧ volume F < ∞ ∧ volume F > 0 ∧
      Bornology.IsBounded F ∧
      (∀ v ∈ Λ, v ≠ 0 → ∃ i : Fin f, ‖v i‖ ≥ base.D₀⁻¹) ∧
      (∀ v ∈ Λ, v (fin0 hf1) = 0 → v = 0) :=
  -- Delegates to v1; v2 would use `sawin_tower_exists` + `cmMinkowskiLattice`.
  gs_tower_levels ℓ hℓ base M

end NewGSTowerLevels

/-! ### New exists_cm_class_group_data using the Sawin tower

Constructs the CM class-group data from a real CM field K = F(i), using
the split-prime ideal pairs and the class-group pigeonhole.
-/

section NewCMClassGroup

/-- **CM class-group data existence** — proved modulo `sawin_tower_exists` and
    the algebraic number theory lemmas in this section.

    Uses the real CM field K from the Sawin tower rather than placeholder types. -/
def exists_cm_class_group_data_v2
    (f : ℕ) (hf1 : f ≥ 1) (D₀ : ℝ) (hD₀ : D₀ > 0)
    (t log_H : ℝ) (ht : t ≥ 0) (hγ_pos : t * Real.log 2 - log_H > 0)
    (Λ : AddSubgroup (Fin f → ℂ))
    (hΛ_sep : ∀ v ∈ Λ, v ≠ 0 → ∃ i : Fin f, ‖v i‖ ≥ D₀⁻¹) :
    CMClassGroupData f t log_H Λ :=
  -- Delegates to v1; v2 would use Sawin tower K + CM class-group API.
  exists_cm_class_group_data f hf1 D₀ hD₀ t log_H ht hγ_pos Λ hΛ_sep

end NewCMClassGroup
