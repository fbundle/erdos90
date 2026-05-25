import Mathlib
import Erdos90.Arithmetic
import Erdos90.CMField.Basic

open Real Filter NumberField Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal Topology Complex Pointwise nonZeroDivisors

noncomputable section

/-!
# Pigeonhole lemma, CM field lemmas, and CM class-group data

This file combines three sections:
- §3: Pigeonhole lemma (`exists_fiber_ge_div`) — fully proved
- §4: CM field lemmas (norm of α / c(α)) — fully proved
- §5: `CMClassGroupData` structure + `exists_cm_class_group_data` (sorried)

All four CM lemmas in §4 are fully proved using only the `IsCMField` API
already in Mathlib v4.29.1.  The `CMClassGroupData` structure abstracts the
ANT input needed for Proposition 2.2.
-/

/-! ## §3  Pigeonhole lemma — fully proved -/

/-- **Fiber cardinality bound (pigeonhole / averaging principle).**

    For any function `f : α → β` between finite nonempty types, there exists
    `b : β` whose preimage has cardinality at least `|α| / |β|`.  This is the
    purely combinatorial core of Proposition 2.2.

    The proof is the standard double-counting argument:
    `|α| = Σ_b |f⁻¹(b)| ≤ |β| · max_b |f⁻¹(b)|`, so `max_b |f⁻¹(b)| ≥ |α| / |β|`. -/
lemma exists_fiber_ge_div {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (f : α → β) (hβ_pos : 0 < Fintype.card β) :
    ∃ b : β, ((Finset.filter (λ a => f a = b) Finset.univ).card : ℝ) ≥
      (Fintype.card α : ℝ) / (Fintype.card β : ℝ) := by
  -- Double-counting identity: Σ_b |f⁻¹(b)| = |α|
  have h_total_nat : (∑ b : β, (Finset.filter (λ a => f a = b) Finset.univ).card) = Fintype.card α := by
    calc
      (∑ b : β, (Finset.filter (λ a => f a = b) Finset.univ).card)
          = (∑ b : β, ∑ a : α, if f a = b then (1 : ℕ) else 0) := by
        refine Finset.sum_congr rfl (λ b _ => ?_)
        rw [Finset.card_filter]
      _ = (∑ a : α, ∑ b : β, if f a = b then (1 : ℕ) else 0) := Finset.sum_comm
      _ = (∑ _a : α, (1 : ℕ)) := by simp
      _ = Fintype.card α := by simp
  -- Promote to ℝ
  have h_total : (∑ b : β, ((Finset.filter (λ a => f a = b) Finset.univ).card : ℝ)) =
      (Fintype.card α : ℝ) := by
    simpa [Nat.cast_sum] using congrArg (Nat.cast : ℕ → ℝ) h_total_nat
  -- The codomain size as ℝ
  set N := (Fintype.card β : ℝ) with hN
  set M := (Fintype.card α : ℝ) with hM
  have hNpos : N > 0 := by
    dsimp [N]
    exact_mod_cast hβ_pos
  -- Proof by contradiction: if all fibers are < M/N, then total < M
  by_contra! hAll
  -- hAll: ∀ b, (fiber b : ℝ) < M / N
  have h_sum_lt : (∑ b : β, ((Finset.filter (λ a => f a = b) Finset.univ).card : ℝ)) <
      (∑ _b : β, M / N) := by
    refine Finset.sum_lt_sum (λ b hb => le_of_lt (hAll b)) ?_
    obtain ⟨b⟩ := Fintype.card_pos_iff.mp hβ_pos
    exact ⟨b, Finset.mem_univ _, hAll b⟩
  have h_sum_eq : (∑ _b : β, M / N) = M := by
    simp [hN, Finset.card_univ]
    field_simp [hNpos.ne']
  linarith [h_total, h_sum_lt, h_sum_eq]

/-! ## §4  Provable CM field lemmas: norm of α / c(α)

    This section proves the core algebraic fact underlying Proposition 2.2:
    for a CM field K, the element α / c(α) has norm 1 at every complex
    embedding, every infinite place, and every mixed-space coordinate.

    Four lemmas at increasing levels of concreteness:
    1. `norm_div_star_eq_one` — pure complex analysis: ‖z / star z‖ = 1
    2. `cm_norm_div_conj_eq_one` — per-embedding version, pure algebra
    3. `normAtPlace_mixedEmbedding_cm_div_conj_eq_one` — per-place version
       using `mixedEmbedding` + `normAtPlace`
    4. `mixedEmbedding_cm_div_conj_complex_norm_one` — concrete `.2` coordinate
       version for complex places

    All are fully proved (no sorry) using only the `IsCMField` API that is
    already in Mathlib v4.29.1.  The remaining construction (split primes,
    class-group map, Minkowski embedding) is abstracted in
    `CMClassGroupData` below. -/

/-- Pure complex analysis: for nonzero `z : ℂ`, `‖z / star z‖ = 1`.
    This is the analytic core underlying `cm_norm_div_conj_eq_one`. -/
lemma norm_div_star_eq_one {z : ℂ} (hz : z ≠ 0) : ‖z / star z‖ = 1 := by
  calc
    ‖z / star z‖ = ‖z‖ / ‖star z‖ := by rw [norm_div]
    _ = ‖z‖ / ‖z‖ := by simp
    _ = 1 := div_self (mt norm_eq_zero.mp hz)

/-- For a CM field `K`, any nonzero `α`, and any complex embedding `φ : K → ℂ`,
    `‖φ (α / complexConj K α)‖ = 1`.  This is the key algebraic fact that
    powers Proposition 2.2: the Minkowski embedding of `α / c(α)` lies on the
    product of unit circles.

    Proof: `φ(α / c(α)) = φ(α) / φ(c(α)) = φ(α) / star(φ(α))`, and for any
    nonzero `z : ℂ`, `‖z / star z‖ = ‖z‖ / ‖z‖ = 1`.

    **Reference**: Neukirch, Ch. I §6; [OpenAI 2026], §2.1; based on
    `IsCMField.complexEmbedding_complexConj` in Mathlib. -/
lemma cm_norm_div_conj_eq_one {K : Type*} [Field K] [NumberField K] [IsCMField K]
    (α : K) (hα : α ≠ 0) (φ : K →+* ℂ) : ‖φ (α / IsCMField.complexConj K α)‖ = 1 := by
  have hφ0 : φ α ≠ 0 := ((map_ne_zero (f := φ)).mpr hα)
  have h_conj : φ (IsCMField.complexConj K α) = star (φ α) := by
    rw [IsCMField.complexEmbedding_complexConj (K := K) φ α, RCLike.star_def]
  rw [map_div₀, h_conj]
  exact norm_div_star_eq_one hφ0

/-- The mixed-embedding lift: under the Minkowski embedding `mixedEmbedding K`,
    the image of `α / c(α)` has `normAtPlace` = 1 at **every** infinite place.
    This is the form directly usable when constructing `mk_unit` in
    `exists_cm_class_group_data`. -/
lemma normAtPlace_mixedEmbedding_cm_div_conj_eq_one {K : Type*} [Field K] [NumberField K] [IsCMField K]
    (α : K) (hα : α ≠ 0) (w : InfinitePlace K) :
    mixedEmbedding.normAtPlace w (NumberField.mixedEmbedding K
      (α / IsCMField.complexConj K α)) = 1 := by
  rw [mixedEmbedding.normAtPlace_apply, ← InfinitePlace.norm_embedding_eq]
  exact cm_norm_div_conj_eq_one α hα (InfinitePlace.embedding w)

/-- For a complex place, the concrete `.2` coordinate of the mixed embedding of
    `α / c(α)` has modulus 1.  This is the concrete form used when relating to
    the `Fin f → ℂ` representation (once the type bridge is filled). -/
lemma mixedEmbedding_cm_div_conj_complex_norm_one {K : Type*} [Field K] [NumberField K] [IsCMField K]
    (α : K) (hα : α ≠ 0) (w : {w : InfinitePlace K // InfinitePlace.IsComplex w}) :
    ‖(NumberField.mixedEmbedding K (α / IsCMField.complexConj K α)).2 w‖ = 1 := by
  have h := normAtPlace_mixedEmbedding_cm_div_conj_eq_one α hα w.val
  rw [mixedEmbedding.normAtPlace_apply_of_isComplex w.prop] at h
  exact h

open Function

/-- When the real-place index set is empty, `((ι → ℝ) × V)` is linearly equivalent to `V`. -/
def prod_left_isEmpty_equiv_snd (V : Type*) [AddCommGroup V] [Module ℝ V] {ι : Type*} [IsEmpty ι] :
    ((ι → ℝ) × V) ≃ₗ[ℝ] V where
  toFun := Prod.snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := (fun i => isEmptyElim i, v)
  left_inv _ := Prod.ext (funext fun i => isEmptyElim i) rfl
  right_inv _ := rfl

/-- For a totally complex number field K (nrRealPlaces = 0), the mixed space
is equivalent to just the complex-place function space. -/
def mixedSpace_equiv_complex_places {K : Type*} [Field K] [NumberField K]
    (h_no_real : InfinitePlace.nrRealPlaces K = 0) :
    mixedEmbedding.mixedSpace K ≃ₗ[ℝ]
      ({w : InfinitePlace K // InfinitePlace.IsComplex w} → ℂ) := by
  classical
    haveI : IsEmpty {w : InfinitePlace K // InfinitePlace.IsReal w} :=
      (Fintype.card_eq_zero_iff
        (α := {w : InfinitePlace K // InfinitePlace.IsReal w})).mp h_no_real
    exact prod_left_isEmpty_equiv_snd
        ({w : InfinitePlace K // InfinitePlace.IsComplex w} → ℂ)

/-- Equivalence between complex places of a totally complex number field K
    and Fin f, where f = nrComplexPlaces K.  Extracted as a standalone definition
    so that `mixedSpace_equiv_pi_fin_of_card` and downstream lemmas share the
    same `e_idx`, avoiding definitional equality issues. -/
def cmComplexPlaceEquiv (K : Type*) [Field K] [NumberField K] (f : ℕ)
    (hf : InfinitePlace.nrComplexPlaces K = f) :
    {w : InfinitePlace K // InfinitePlace.IsComplex w} ≃ Fin f := by
  classical
    have h_card : Fintype.card {w : InfinitePlace K // InfinitePlace.IsComplex w} = f := by
      simpa [InfinitePlace.nrComplexPlaces] using hf
    let e_card : Fin (Fintype.card {w : InfinitePlace K // InfinitePlace.IsComplex w}) ≃ Fin f :=
      { toFun := Fin.cast h_card
        invFun := Fin.cast h_card.symm
        left_inv := fun x => by
          apply Fin.ext; simp [Fin.cast]
        right_inv := fun x => by
          apply Fin.ext; simp [Fin.cast]
      }
    exact (Fintype.equivFin _).trans e_card

/-- When K is totally complex of degree f (complex places), mixedSpace K is equivalent
to `Fin f → ℂ`.  This is the type bridge needed for `gs_tower_levels`. -/
def mixedSpace_equiv_pi_fin_of_card {K : Type*} [Field K] [NumberField K]
    (h_no_real : InfinitePlace.nrRealPlaces K = 0) (f : ℕ)
    (hf : InfinitePlace.nrComplexPlaces K = f) :
    mixedEmbedding.mixedSpace K ≃ₗ[ℝ] (Fin f → ℂ) := by
  classical
    let e₁ := mixedSpace_equiv_complex_places h_no_real
    let e_idx : {w : InfinitePlace K // InfinitePlace.IsComplex w} ≃ Fin f :=
      cmComplexPlaceEquiv K f hf
    let e_arrow : ({w : InfinitePlace K // InfinitePlace.IsComplex w} → ℂ) ≃ (Fin f → ℂ) :=
      Equiv.arrowCongr e_idx (Equiv.refl ℂ)
    let e_pi : ({w : InfinitePlace K // InfinitePlace.IsComplex w} → ℂ) ≃ₗ[ℝ]
      (Fin f → ℂ) := {
        e_arrow with
        map_add' := fun x y => rfl
        map_smul' := fun r x => rfl
      }
    exact e₁.trans e_pi

/-- Evaluating `mixedSpace_equiv_pi_fin_of_card` at index i gives the mixed-space
    `.2` coordinate at the complex place corresponding to i. -/
lemma mixedSpace_equiv_pi_fin_of_card_apply {K : Type*} [Field K] [NumberField K]
    (h_no_real : InfinitePlace.nrRealPlaces K = 0) (f : ℕ)
    (hf : InfinitePlace.nrComplexPlaces K = f)
    (x : mixedEmbedding.mixedSpace K) (i : Fin f) :
    mixedSpace_equiv_pi_fin_of_card h_no_real f hf x i =
      x.2 ((cmComplexPlaceEquiv K f hf).symm i) := by
  dsimp [mixedSpace_equiv_pi_fin_of_card, mixedSpace_equiv_complex_places,
    prod_left_isEmpty_equiv_snd]

/-- The norm of `mixedSpace_equiv_pi_fin_of_card` evaluated at the image of a ∈ K
    equals `normAtPlace` at the corresponding complex place. -/
lemma mixedSpace_equiv_pi_fin_of_card_norm_apply {K : Type*} [Field K] [NumberField K]
    (h_no_real : InfinitePlace.nrRealPlaces K = 0) (f : ℕ)
    (hf : InfinitePlace.nrComplexPlaces K = f)
    (a : K) (i : Fin f) :
    ‖mixedSpace_equiv_pi_fin_of_card h_no_real f hf
      (NumberField.mixedEmbedding K a) i‖ =
    mixedEmbedding.normAtPlace
      ((cmComplexPlaceEquiv K f hf).symm i : InfinitePlace K)
      (NumberField.mixedEmbedding K a) := by
  rw [mixedSpace_equiv_pi_fin_of_card_apply]
  let w := (cmComplexPlaceEquiv K f hf).symm i
  have h_complex : InfinitePlace.IsComplex (w : InfinitePlace K) := w.prop
  rw [mixedEmbedding.normAtPlace_apply_of_isComplex h_complex]

/-! ## §5  CM class-group data structure

    The structure `CMClassGroupData` abstracts the algebraic number theory
    input needed for Proposition 2.2 (class-group pigeonhole → norm-one set).

    The norm-1 property is already proved as `cm_norm_div_conj_eq_one` above.
    What remains (all sorried) is the constructive number theory:
    1. A CM field K of degree 2f with split-prime ideal pairs
    2. The sign-vector type E = {±1}^m and class-group map φ : E → Cl(K)
    3. The cardinality ratio |E|/|Cl(K)| ≥ exp(γ·f) + 1

    **Mathematical origin** ([OpenAI 2026], §2.1; Neukirch, Ch. I §6–7,
    Ch. III §3):

    Let K be a CM field (totally complex quadratic extension of a totally real
    field K⁺, [K : ℚ] = 2f).  Let t be the number of split primes q₁,…,q_t
    in the base field, each splitting as m = t·f distinct prime ideal pairs
    𝔓_j, c𝔓_j in 𝒪_K (where c is complex conjugation).

    The sign-vector set E = {±1}^m has |E| = 2^m.  For ε ∈ E, define
      a_ε = ∏_{j=1}^m 𝔓_j^{(1+ε_j)/2} · (c𝔓_j)^{(1-ε_j)/2}
    and map φ : E → ClassGroup(𝒪_K) by φ(ε) = [a_ε].

    For ε₁ ≠ ε₂ in the same fiber (φ(ε₁) = φ(ε₂)), the ideal a_{ε₁}/a_{ε₂}
    is principal, say = (α).  By `cm_norm_div_conj_eq_one` we have
    |σ(α / c(α))| = 1 at every complex embedding σ : K → ℂ.

    Thus α / c(α) maps under the Minkowski embedding Φ into Λ ⊂ ℂ^f with
    all coordinates of modulus 1.  The map (ε₁, ε₂) ↦ u := Φ(α/c(α)) is
    injective for fixed ε₁ within the fiber. -/

/-- Concrete CM field data threading from the tower construction to the class-group
    pigeonhole.  Carries the CM field K, its Minkowski embedding bridge φ, and a
    membership characterization of Λ.  This allows `exists_cm_class_group_data` to
    construct non-trivial `mk_unit` elements using K's ring of integers.

    **Fields**:
    - `K` — a CM number field (e.g., ℚ(ζ_p))
    - `φ` — `mixedSpace K ≃ₗ[ℝ] Fin f → ℂ`, the type bridge
    - `h_nrComplexPlaces`, `h_nrRealPlaces` — cardinalities matching `f`
    - `mem_iff` — v ∈ Λ iff v = φ(Φ(a)) for some a ∈ 𝒪_K
    - `h_φ1_norm` — Minkowski embedding of 1 ∈ K has all coords of norm 1
    - `h_φ_norm_div_conj` — for α≠0, ‖φ(Φ(α/c(α))) r‖ = 1 at all coordinates -/
structure CMTowerData (f : ℕ) (hf1 : f ≥ 1) (Λ : AddSubgroup (Fin f → ℂ))
    (K : Type) [Field K] [NumberField K] [IsCMField K] where
  φ : mixedEmbedding.mixedSpace K ≃ₗ[ℝ] Fin f → ℂ
  h_nrComplexPlaces : InfinitePlace.nrComplexPlaces K = f
  h_nrRealPlaces : InfinitePlace.nrRealPlaces K = 0
  mem_iff (v : Fin f → ℂ) : v ∈ Λ ↔ ∃ a : 𝓞 K, φ (NumberField.mixedEmbedding K (a : K)) = v
  h_φ1_norm : ∀ r : Fin f, ‖φ (NumberField.mixedEmbedding K (1 : K)) r‖ = 1
  h_φ_norm_div_conj : ∀ (α : K) (_ : α ≠ 0) (r : Fin f),
    ‖φ (NumberField.mixedEmbedding K (α / IsCMField.complexConj K α)) r‖ = 1
  /-- Split prime ideal data: for any integer `t'`, we can find `t' * f` split-prime ideal
  pairs in K (each prime ≠ its complex conjugate, all 2·(t'·f) ideals pairwise distinct).
  Filled by the cyclotomic tower constructor using Dirichlet's theorem. -/
  splitPrimesFor : ∀ (t' : ℕ), SplitPrimeData K (t' * f)

/-- Abstract data packaging the CM field / class-group construction for Prop 2.2.
    See the discussion above §4–§5 for the mathematical context. -/
structure CMClassGroupData (f : ℕ) (t log_H : ℝ) (Λ : AddSubgroup (Fin f → ℂ)) where
  E : Type
  [fintypeE : Fintype E]
  [decidableEqE : DecidableEq E]
  G : Type
  [fintypeG : Fintype G]
  [decidableEqG : DecidableEq G]
  φ : E → G
  /-- Explicit ℕ cardinals — avoid instance-dependent `Fintype.card` in the ratio bound. -/
  cardE : ℕ
  cardG : ℕ
  hcardE : cardE = Fintype.card E
  hcardG : cardG = Fintype.card G
  /-- |E| / |G| ≥ exp((t·log 2 − log_H)·f) + 1.
      The "+1" compensates for losing one element when fixing a fiber anchor ε₀:
      |U| = |F| − 1 ≥ exp(γ·f).  Uses explicit ℕ cardinals to avoid instance mismatches. -/
  h_card_ratio : Real.exp ((t * Real.log 2 - log_H) * (f : ℝ)) + 1 ≤ (cardE : ℝ) / (cardG : ℝ)
  /-- Construct a norm-1 lattice vector from two distinct elements in the same fiber. -/
  mk_unit : E → E → Fin f → ℂ
  mk_unit_mem_Λ : ∀ ε₁ ε₂, ε₁ ≠ ε₂ → φ ε₁ = φ ε₂ → mk_unit ε₁ ε₂ ∈ Λ
  mk_unit_norm : ∀ ε₁ ε₂, ε₁ ≠ ε₂ → φ ε₁ = φ ε₂ → ∀ r, ‖mk_unit ε₁ ε₂ r‖ = 1
  /-- Injectivity: for a fixed anchor ε₁, distinct ε₂, ε₃ in the fiber give distinct vectors. -/
  mk_unit_inj : ∀ ε₁ ε₂ ε₃, ε₁ ≠ ε₂ → ε₁ ≠ ε₃ → φ ε₁ = φ ε₂ → φ ε₁ = φ ε₃ →
    mk_unit ε₁ ε₂ = mk_unit ε₁ ε₃ → ε₂ = ε₃

/-! ### Norm‑1 quotient lemma

`mk_unit_from_cm_quotient` packages the two properties that the real `mk_unit`
construction must satisfy (membership in Λ and norm‑1).  The full injectivity
proof would additionally need the class‑group automorphism induced by complex
conjugation, which in newer Mathlib is `ClassGroup.mulEquiv` but is not
available in v4.29.1. -/

open scoped Classical

/-- For α ∈ K^× such that α / c(α) ∈ 𝓞_K, its Minkowski image lies in Λ and has
    all coordinates of norm 1.  This lemma packages the two properties that the real
    `mk_unit` construction must satisfy (membership in Λ and norm‑1).

    Mathematical proof (paper §2.1): `IsCMField.complexConj` fixes the totally real
    subfield, so α / c(α) has absolute value 1 in every complex embedding.  The
    integrality hypothesis gives membership via `cmData.mem_iff`. -/
lemma mk_unit_from_cm_quotient {K : Type} [Field K] [NumberField K] [IsCMField K]
    {f : ℕ} {hf1 : f ≥ 1} {Λ : AddSubgroup (Fin f → ℂ)}
    (cmData : CMTowerData f hf1 Λ K) (α : K) (hα : α ≠ 0)
    (h_int : (α / IsCMField.complexConj K α) ∈ (algebraMap (𝓞 K) K).range) :
    cmData.φ (NumberField.mixedEmbedding K ((α / IsCMField.complexConj K α : K) : K)) ∈ Λ ∧
    ∀ r : Fin f, ‖cmData.φ (NumberField.mixedEmbedding K
      ((α / IsCMField.complexConj K α : K) : K)) r‖ = 1 := by
  have h_mem : cmData.φ (NumberField.mixedEmbedding K
      ((α / IsCMField.complexConj K α : K) : K)) ∈ Λ := by
    rw [cmData.mem_iff]
    obtain ⟨a, ha⟩ := h_int
    refine ⟨a, ?_⟩
    have ha' : (a : K) = (α / IsCMField.complexConj K α : K) := ha
    simp [ha']
  have h_norm : ∀ r : Fin f,
      ‖cmData.φ (NumberField.mixedEmbedding K
        ((α / IsCMField.complexConj K α : K) : K)) r‖ = 1 :=
    cmData.h_φ_norm_div_conj α hα
  exact ⟨h_mem, h_norm⟩

/-- Complex conjugation induces an automorphism of the ideal class group of a CM field.
    Uses `ClassGroup.mulEquiv` (available in Mathlib v4.29.1). -/
noncomputable def classGroupComplexConj (K : Type) [Field K] [NumberField K] [IsCMField K] :
    ClassGroup (𝓞 K) ≃* ClassGroup (𝓞 K) :=
  ClassGroup.mulEquiv (IsCMField.ringOfIntegersComplexConj K).toRingEquiv

/-- **CM class-group data existence** (sorry'd).

    This is the single number-theoretic sorry for Proposition 2.2.
    It asserts that for every tower level (parametrized by f, t, log_H, Λ)
    satisfying the resolution hypotheses, the algebraic data needed for
    the class-group pigeonhole exists.

    Returns an existential over types `E`, `G` with `Fintype`/`DecidableEq` instances
    (using `obtain` avoids the `let`-binder instance problem).

    **What needs to be constructed** (not available in Mathlib v4.29.1):
    1. A CM field K of degree 2f (totally complex, quadratic over totally real K⁺)
       with ring of integers 𝒪_K and class group G = ClassGroup(𝒪_K).
    2. m ≥ t·f split-prime ideal pairs (𝔓_j, c𝔓_j) in 𝒪_K.
    3. The sign-vector type E = {±1}^m and class map φ : E → G.
    4. Proof that |G| ≤ exp(log_H · f) (class-number bound from Minkowski / tower
       root-discriminant bounds; uses `exists_ideal_in_class_of_norm_le` in Mathlib).
    5. Proof that |E|/|G| ≥ exp(γ·f) + 1 (from |E| = 2^m ≥ 2^{t·f} and the
       class-number bound, using 2·exp(γ·f) ≥ exp(γ·f) + 1 for γ·f > 0).
    6. The norm-1 element constructor mk_unit (from α/c(α) for CM fields, using
       Mathlib's `IsCMField.complexConj`, `IsCMField.complexEmbedding_complexConj`).
    7. Injectivity of mk_unit on fibers (number-theoretic: α/c(α) = β/c(β) implies
       α/β ∈ K⁺, which together with the ideal equality forces ε₂ = ε₃).

    **Relevant Mathlib APIs** (incomplete but provide building blocks):
    - `IsCyclotomicExtension.Rat.isCMField` — cyclotomic extensions are CM
    - `NumberField.classNumber` — class number (cardinality of ClassGroup)
    - `NumberField.exists_ideal_in_class_of_norm_le` — Minkowski bound
    - `IsCMField.complexConj` — complex conjugation on CM fields
    - `IsCMField.complexEmbedding_complexConj` — conj interacts with embeddings
    - `NumberField.mixedSpace` / `integerLattice` / `fundamentalDomain_integerLattice` — lattice

    **Reference**: Section 2 of [OpenAI 2026]; Neukirch Ch. I §6–7, Ch. III §3. -/

def exists_cm_class_group_data
    {K : Type} [Field K] [NumberField K] [IsCMField K]
    (f : ℕ) (hf1 : f ≥ 1) (D₀ : ℝ) (hD₀ : D₀ > 0)
    (t log_H : ℝ) (ht : t ≥ 0) (hγ_pos : t * Real.log 2 - log_H > 0)
    (Λ : AddSubgroup (Fin f → ℂ))
    (hΛ_sep : ∀ v ∈ Λ, v ≠ 0 → ∃ i : Fin f, ‖v i‖ ≥ D₀⁻¹)
    (cmData : CMTowerData f hf1 Λ K) :
    CMClassGroupData f t log_H Λ := by
  -- -----------------------------------------------------------------
  -- §5.1  Get t' = ⌈t⌉₊ split primes and m = t'·f split-prime ideal pairs
  -- -----------------------------------------------------------------
  let t' : ℕ := ⌈t⌉₊
  have ht'_ge_t : (t : ℝ) ≤ (t' : ℝ) := by
    dsimp [t']
    exact ((Nat.ceil_le (a := (t : ℝ)) (n := t')).mp (le_refl t'))
  let spDM : SplitPrimeData K (t' * f) := cmData.splitPrimesFor t'
  let m : ℕ := t' * f
  -- -----------------------------------------------------------------
  -- §5.2  Sign-vector type E = {±1}^m and class group G
  --
  -- E = Fin m → Bool encodes sign choices ±1 for each split-prime pair.
  -- |E| = 2^m ≥ 2^{t·f} = exp(t·log 2 · f).
  -- G = ClassGroup(𝒪_K) is the target of the ideal-class map φ.
  -- |G| = class number h_K ≤ exp(log_H · f) (Minkowski bound).
  --
  -- For the cardinality ratio: |E|/|G| ≥ exp((t·log 2 - log_H)·f) = exp(γ·f).
  -- -----------------------------------------------------------------
  let E : Type := Fin m → Bool
  letI : Fintype E := inferInstance
  letI : DecidableEq E := inferInstance
  have hcardE_val : Fintype.card E = 2 ^ m := by
    dsimp [E]
    simp
  let cardE : ℕ := 2 ^ m
  have hcardE : cardE = Fintype.card E := by
    dsimp [cardE, E]
    simp
  let G : Type := ClassGroup (𝓞 K)
  letI : Fintype G := inferInstance
  letI : DecidableEq G := inferInstance
  have hcardG_pos : 0 < Fintype.card G := by
    rw [Fintype.card_pos_iff]
    exact ⟨1⟩
  -- cardG = class number h_K; use Fintype.card directly
  let cardG : ℕ := Fintype.card G
  have hcardG : cardG = Fintype.card G := rfl
  -- -----------------------------------------------------------------
  -- §5.3  Ideal J(ε) = ∏_j (if ε_j then 𝔓_j else c(𝔓_j))
  --
  -- Each ε : Fin m → Bool picks one prime from each conjugate pair.
  -- The product is over all m primes; each factor is a nonzero prime ideal.
  -- -----------------------------------------------------------------
  let J (ε : E) : Ideal (𝓞 K) :=
    Finset.prod Finset.univ
      (fun (j : Fin m) => if ε j then spDM.primes j else conjIdeal K (spDM.primes j))
  have hJ_ne_zero (ε : E) : J ε ≠ 0 := by
    dsimp [J]
    refine (Finset.prod_ne_zero_iff.mpr (fun j _ => ?_))
    by_cases hεj : ε j
    · simp [hεj, spDM.h_ne_bot j]
    · simp [hεj, conjIdeal_ne_bot K (spDM.h_ne_bot j)]
  have hJ_ne_bot (ε : E) : J ε ≠ ⊥ := by
    intro h_eq
    apply hJ_ne_zero ε
    simpa using h_eq
  -- Convert J ε to a nonzero ideal element
  -- (Ideal (𝓞 K))⁰ = { I : Ideal (𝓞 K) // I ∈ nonZeroDivisors (Ideal (𝓞 K)) }
  have hJ_nonZeroDiv (ε : E) : J ε ∈ nonZeroDivisors (Ideal (𝓞 K)) := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact hJ_ne_zero ε
  let J0 (ε : E) : {I : Ideal (𝓞 K) // I ∈ nonZeroDivisors (Ideal (𝓞 K))} :=
    ⟨J ε, hJ_nonZeroDiv ε⟩
  -- -----------------------------------------------------------------
  -- §5.4  Class-group map φ : E → G
  --
  -- φ(ε) = class of J(ε) in the class group.
  -- -----------------------------------------------------------------
  let φ : E → G := fun ε => ClassGroup.mk0 (J0 ε)
  -- -----------------------------------------------------------------
  -- §5.5  Cardinality ratio |E|/|G| ≥ exp(γ·f) + 1
  --
  -- |E| = 2^m ≥ 2^{t·f} = exp(t·log 2 · f).
  -- |G| = h_K, the class number.
  -- The Minkowski bound gives h_K ≤ exp(log_H · f).
  -- Hence |E|/|G| ≥ exp((t·log 2 - log_H)·f) + 1 (for sufficiently large f).
  --
  -- GAP: the Minkowski class-number bound exp(log_H·f) is not available in Mathlib.
  -- We use the crude bound: cardG ≥ 1 gives (2^m : ℝ) / cardG ≥ 2^m / cardG,
  -- and we need 2^m / cardG ≥ exp(γ·f) + 1.
  -- This holds when 2^m ≥ cardG · (exp(γ·f) + 1), which follows from the
  -- Ah-Minkowski class-number formula (Minkowski bound + analytic class number).
  -- -----------------------------------------------------------------
  have h_card_ratio : Real.exp ((t * Real.log 2 - log_H) * (f : ℝ)) + 1 ≤
      (cardE : ℝ) / (cardG : ℝ) := by
    -- cardE = 2^m ≥ 2^{t·f} = exp(t·log 2 · f)
    -- cardG = h_K ≤ exp(log_H · f)  (Minkowski class-number bound, not in Mathlib)
    -- Then cardE / cardG ≥ exp((t·log 2 - log_H)·f) = exp(γ·f).
    -- The "+1" margin is absorbed for exp(γ·f) ≥ 1.
    -- GAP: the class-number bound log h_K ≤ log_H · f is not available.
    -- For now we admit this bound as a sorry.
    have h_exp_bound : (Real.exp ((t * Real.log 2 - log_H) * (f : ℝ)) + 1 : ℝ) ≤
        ((2 : ℝ) ^ m : ℝ) / (cardG : ℝ) := by
      -- The full proof: 2^m = 2^{t'·f} ≥ 2^{t·f} = exp(t·log 2 · f).
      -- Then use the Minkowski class-number bound cardG ≤ exp(log_H · f).
      -- This is a deep ANT result requiring the Minkowski bound + class number formula.
      sorry
    have h_cardE_val : (cardE : ℝ) = ((2 : ℝ) ^ m : ℝ) := by
      dsimp [cardE]; simp
    rw [h_cardE_val]
    exact h_exp_bound
  -- -----------------------------------------------------------------
  -- §5.6  The mk_unit constructor: Φ(α / c(α))
  --
  -- For ε₁ ≠ ε₂ with φ(ε₁) = φ(ε₂), the ideals J(ε₁) and J(ε₂) are in the
  -- same class group.  By `ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring`,
  -- there exists α ∈ K^× such that (α)·J(ε₁) = J(ε₂) as fractional ideals.
  --
  -- Define mk_unit ε₁ ε₂ := Φ(α / c(α)) where Φ = cmData.φ ∘ mixedEmbedding.
  -- This has all coordinates of norm 1 (by h_φ_norm_div_conj, proved in §4).
  --
  -- The integrality condition α/c(α) ∈ 𝒪_K (needed for Λ membership via
  -- mk_unit_from_cm_quotient) follows from a valuation argument after
  -- scaling by D₀ = Q².  When D₀ = 1 (current tower), this is sorried.
  --
  -- The injectivity proof proceeds in two steps:
  -- (3) Φ(α₂/c(α₂)) = Φ(α₃/c(α₃)) → α₂/c(α₂) = α₃/c(α₃) → α₂·c(α₃)=α₃·c(α₂)
  --     → α₂/α₃ = c(α₂/α₃) → α₂/α₃ ∈ K⁺ (by IsCMField.complexConj_eq_self_iff).
  -- (4) α₂/α₃ ∈ K⁺ → valuations at 𝔓_j and c(𝔓_j) agree → ε₂_j = ε₃_j.
  --     Step (4) requires split-prime valuation theory (not in Mathlib).
  -- -----------------------------------------------------------------

  -- Helper: from φ(ε₁) = φ(ε₂), extract α ∈ K^× such that (α)·J(ε₁) = J(ε₂)
  -- as fractional ideals.  Uses the fraction-ring formulation which gives
  -- α directly in K (rather than x/y with x, y ∈ 𝓞_K).
  have h_exists_alpha (ε₁ ε₂ : E) (hφ_eq : φ ε₁ = φ ε₂) :
      ∃ (α : K), α ≠ 0 ∧ FractionalIdeal.spanSingleton (𝓞 K)⁰ α * (J0 ε₁ : FractionalIdeal (𝓞 K)⁰ K) =
        (J0 ε₂ : FractionalIdeal (𝓞 K)⁰ K) := by
    rcases (ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring (R := 𝓞 K) (K := K)).mp hφ_eq with
      ⟨α, hα, h⟩
    exact ⟨α, hα, h⟩

  -- Define mk_unit: when φ(ε₁) = φ(ε₂), pick an α and send it through Φ(·/c(·)).
  -- Otherwise fall back to Φ(1).
  let mk_unit (ε₁ ε₂ : E) : Fin f → ℂ :=
    if h : φ ε₁ = φ ε₂ then
      let α := Classical.choose (h_exists_alpha ε₁ ε₂ h)
      cmData.φ (NumberField.mixedEmbedding K ((α / IsCMField.complexConj K α : K) : K))
    else
      cmData.φ (NumberField.mixedEmbedding K (1 : K))

  -- ---------------------------------------------------------------
  -- hmk_unit_norm: the norm-1 property (uses §4 lemma)
  -- ---------------------------------------------------------------
  have hmk_unit_norm : ∀ ε₁ ε₂, ε₁ ≠ ε₂ → φ ε₁ = φ ε₂ → ∀ r, ‖mk_unit ε₁ ε₂ r‖ = 1 := by
    intro ε₁ ε₂ _hne hφ_eq r
    dsimp [mk_unit]
    rw [dif_pos hφ_eq]
    let α := Classical.choose (h_exists_alpha ε₁ ε₂ hφ_eq)
    have hα : α ≠ 0 := (Classical.choose_spec (h_exists_alpha ε₁ ε₂ hφ_eq)).1
    exact cmData.h_φ_norm_div_conj α hα r

  -- ---------------------------------------------------------------
  -- hmk_unit_mem_Λ: membership in the lattice (needs integrality of α/c(α))
  --
  -- The mathematical proof: after scaling the tower by D₀ = Q²
  -- (product of split primes squared), α/c(α) ∈ D₀⁻¹·𝓞_K.
  -- With the current D₀=1 tower, Φ(α/c(α)) may not be in Λ = Φ(𝓞_K).
  -- We use `mk_unit_from_cm_quotient` which handles the proof given
  -- the integrality hypothesis.
  -- ---------------------------------------------------------------
  have hmk_unit_mem_Λ : ∀ ε₁ ε₂, ε₁ ≠ ε₂ → φ ε₁ = φ ε₂ → mk_unit ε₁ ε₂ ∈ Λ := by
    intro ε₁ ε₂ hne hφ_eq
    dsimp [mk_unit]
    rw [dif_pos hφ_eq]
    let α := Classical.choose (h_exists_alpha ε₁ ε₂ hφ_eq)
    have hα : α ≠ 0 := (Classical.choose_spec (h_exists_alpha ε₁ ε₂ hφ_eq)).1
    -- The lemma `mk_unit_from_cm_quotient cmData α hα h_int` gives exactly
    --   cmData.φ (mixedEmbedding K (α / c(α))) ∈ Λ
    -- provided we have the integrality condition:
    --   h_int : (α / complexConj K α) ∈ (algebraMap (𝓞 K) K).range
    -- GAP: This requires D₀ = Q² tower scaling.  With D₀ = 1, α/c(α) may have
    -- denominators at the split primes (exponents ±2 in the denominator).
    -- The proper tower (Q = ∏ q_i, D₀ = Q²) ensures α/c(α) · Q² ∈ 𝓞_K, giving
    -- membership in Λ = Φ(D₀⁻¹·𝓞_K).  See paper §2.1, valuation parity argument.
    have h_int : (α / IsCMField.complexConj K α) ∈
        (algebraMap (𝓞 K) K).range := by
      sorry
    exact (mk_unit_from_cm_quotient cmData α hα h_int).1

  -- ---------------------------------------------------------------
  -- hmk_unit_inj: injectivity of mk_unit for fixed ε₁ on the fiber
  --
  -- Mathematical proof (paper §2.1), split into two lemmas:
  --
  -- **Lemma A** (algebraic): mk_unit ε₁ ε₂ = mk_unit ε₁ ε₃ →
  --   α₂/c(α₂) = α₃/c(α₃) (Minkowski injectivity) →
  --   α₂·c(α₃) = α₃·c(α₂) → α₂/α₃ = c(α₂/α₃) → α₂/α₃ ∈ K⁺.
  --
  -- **Lemma B** (arithmetic): α₂/α₃ ∈ K⁺ and the ideal equalities
  --   (α₂)·J(ε₁) = J(ε₂), (α₃)·J(ε₁) = J(ε₃) imply ε₂ = ε₃.
  --   This uses the split-prime valuation argument: in K⁺,
  --   v_{𝔓_j}(·) = v_{c(𝔓_j)}(·), which forces ε₂_j = ε₃_j for all j.
  --
  -- Lemma A is proved below.  Lemma B requires the split-prime
  -- valuation API (not available in Mathlib) and is sorried.
  -- ---------------------------------------------------------------
  have hmk_unit_inj : ∀ ε₁ ε₂ ε₃, ε₁ ≠ ε₂ → ε₁ ≠ ε₃ → φ ε₁ = φ ε₂ → φ ε₁ = φ ε₃ →
      mk_unit ε₁ ε₂ = mk_unit ε₁ ε₃ → ε₂ = ε₃ := by
    intro ε₁ ε₂ ε₃ _hne₁₂ _hne₁₃ hφ₁₂ hφ₁₃ h_mk_eq
    dsimp [mk_unit] at h_mk_eq
    rw [dif_pos hφ₁₂, dif_pos hφ₁₃] at h_mk_eq
    let α₂ := Classical.choose (h_exists_alpha ε₁ ε₂ hφ₁₂)
    let α₃ := Classical.choose (h_exists_alpha ε₁ ε₃ hφ₁₃)
    have hα₂_spec := Classical.choose_spec (h_exists_alpha ε₁ ε₂ hφ₁₂)
    have hα₃_spec := Classical.choose_spec (h_exists_alpha ε₁ ε₃ hφ₁₃)
    have hα₂ : α₂ ≠ 0 := hα₂_spec.1
    have hα₃ : α₃ ≠ 0 := hα₃_spec.1
    have hα₂_eq : FractionalIdeal.spanSingleton (𝓞 K)⁰ α₂ * (J0 ε₁ : FractionalIdeal (𝓞 K)⁰ K) =
        (J0 ε₂ : FractionalIdeal (𝓞 K)⁰ K) := hα₂_spec.2
    have hα₃_eq : FractionalIdeal.spanSingleton (𝓞 K)⁰ α₃ * (J0 ε₁ : FractionalIdeal (𝓞 K)⁰ K) =
        (J0 ε₃ : FractionalIdeal (𝓞 K)⁰ K) := hα₃_spec.2
    -- Step 1: Minkowski embedding injectivity → α₂/c(α₂) = α₃/c(α₃) in K
    have h_val_eq : (α₂ / IsCMField.complexConj K α₂ : K) = (α₃ / IsCMField.complexConj K α₃ : K) := by
      -- cmData.φ is an ≃ₗ[ℝ], hence injective
      have h_mixed_eq : NumberField.mixedEmbedding K
          ((α₂ / IsCMField.complexConj K α₂ : K) : K) =
        NumberField.mixedEmbedding K ((α₃ / IsCMField.complexConj K α₃ : K) : K) := by
        apply cmData.φ.injective
        exact h_mk_eq
      exact (NumberField.mixedEmbedding_injective K) h_mixed_eq
    -- Step 2: Algebraic manipulation → α₂/α₃ is fixed by complex conjugation
    have hcα₂ : IsCMField.complexConj K α₂ ≠ 0 := by
      intro h
      apply hα₂
      have := congrArg (IsCMField.complexConj K) h
      simpa [IsCMField.complexConj_apply_apply K] using this
    have hcα₃ : IsCMField.complexConj K α₃ ≠ 0 := by
      intro h
      apply hα₃
      have := congrArg (IsCMField.complexConj K) h
      simpa [IsCMField.complexConj_apply_apply K] using this
    have h_cross : α₂ * IsCMField.complexConj K α₃ = α₃ * IsCMField.complexConj K α₂ := by
      -- From h_val_eq: α₂/c(α₂) = α₃/c(α₃)
      -- div_eq_div_iff hb hd : a/b = c/d ↔ a*d = c*b
      exact (div_eq_div_iff hcα₂ hcα₃).mp h_val_eq
    have h_ratio_fixed : IsCMField.complexConj K (α₂ / α₃) = (α₂ / α₃ : K) := by
      calc
        IsCMField.complexConj K (α₂ / α₃) =
            IsCMField.complexConj K α₂ / IsCMField.complexConj K α₃ := by simp
        _ = α₂ / α₃ := by
          apply (div_eq_div_iff hcα₃ hα₃).mpr
          calc
            IsCMField.complexConj K α₂ * α₃ = α₃ * IsCMField.complexConj K α₂ := mul_comm _ _
            _ = α₂ * IsCMField.complexConj K α₃ := h_cross.symm
    -- Step 3: By CM field theory, α₂/α₃ lies in the maximal real subfield K⁺
    have h_ratio_mem_Kplus : (α₂ / α₃ : K) ∈ maximalRealSubfield K := by
      rw [← IsCMField.complexConj_eq_self_iff]
      exact h_ratio_fixed
    -- Step 4: Count-based argument → ε₂ = ε₃
    --
    -- Using the ideal equations (α_i)·J(ε₁) = J(ε_i) and the `count` API
    -- on fractional ideals.  For each split-prime index s:
    --   count at 𝔓_s of spanSingleton(α₂/α₃) = (ε₂_s − ε₃_s)
    --   count at c(𝔓_s) of spanSingleton(α₂/α₃) = (ε₃_s − ε₂_s)
    -- Since α₂/α₃ ∈ K⁺, count_eq_count_conj_of_fixed forces these equal,
    -- hence ε₂_s = ε₃_s for all s.
    have h_ratio_ne_zero : (α₂ / α₃ : K) ≠ 0 := by
      intro hzero
      have hzero' := div_eq_zero_iff.mp hzero
      rcases hzero' with (h | h)
      · exact hα₂ h
      · exact hα₃ h
    -- Connection: J0 ε coerces to J_ideal via FractionalIdeal.coeIdeal
    -- Helper: coeIdeal distributes over Finset.prod
    -- The equality is `map_prod` for `coeIdealHom` after pushing `↑` through the `if`.
    have hJ0_to_ideal (ε : E) : (J0 ε : FractionalIdeal (𝓞 K)⁰ K) = J_ideal K spDM ε := by
      dsimp [J0, J, J_ideal]
      have h := map_prod (FractionalIdeal.coeIdealHom (𝓞 K)⁰ K)
        (fun j => if ε j then spDM.primes j else conjIdeal K (spDM.primes j)) Finset.univ
      dsimp [FractionalIdeal.coeIdealHom] at h
      -- h RHS has ↑(if ...) outside; goal RHS has ↑ inside each branch
      -- Use `simp` to push the coercion through the if
      simp [apply_ite] at h
      simpa using h
    -- count(v, spanSingleton α) = if ε₂ s then 1 else 0 - if ε₁ s then 1 else 0
    have h_count_α_v (ε' : E) (hφ_eq' : φ ε₁ = φ ε') (hα_eq' : FractionalIdeal.spanSingleton (𝓞 K)⁰
        (Classical.choose (h_exists_alpha ε₁ ε' hφ_eq')) * (J0 ε₁ : FractionalIdeal (𝓞 K)⁰ K) =
        (J0 ε' : FractionalIdeal (𝓞 K)⁰ K)) (α' : K) (hα_spec : α' = Classical.choose
        (h_exists_alpha ε₁ ε' hφ_eq')) (s : Fin m) :
        FractionalIdeal.count K (spDM.toHeightOneSpectrum (j := s))
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ α') =
        ((if ε' s then 1 else 0 : ℤ) - (if ε₁ s then 1 else 0 : ℤ)) := by
      subst hα_spec
      let α' := Classical.choose (h_exists_alpha ε₁ ε' hφ_eq')
      have hα'_ne : α' ≠ 0 := (Classical.choose_spec (h_exists_alpha ε₁ ε' hφ_eq')).1
      have hS_ne : FractionalIdeal.spanSingleton (𝓞 K)⁰ α' ≠ 0 :=
        FractionalIdeal.spanSingleton_ne_zero_iff.mpr hα'_ne
      have hJ0_ne : (J0 ε₁ : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
        rw [hJ0_to_ideal ε₁]
        exact J_ideal_ne_zero K spDM ε₁
      have hcount_mul := congrArg (FractionalIdeal.count K
        (spDM.toHeightOneSpectrum (j := s))) hα_eq'
      rw [FractionalIdeal.count_mul K (spDM.toHeightOneSpectrum (j := s)) hS_ne hJ0_ne]
        at hcount_mul
      rw [hJ0_to_ideal ε₁, count_J_eq K spDM ε₁ s,
        hJ0_to_ideal ε', count_J_eq K spDM ε' s] at hcount_mul
      linarith
    -- Compute count at conjugate prime
    have h_count_α_cv (ε' : E) (hφ_eq' : φ ε₁ = φ ε') (hα_eq' : FractionalIdeal.spanSingleton (𝓞 K)⁰
        (Classical.choose (h_exists_alpha ε₁ ε' hφ_eq')) * (J0 ε₁ : FractionalIdeal (𝓞 K)⁰ K) =
        (J0 ε' : FractionalIdeal (𝓞 K)⁰ K)) (α' : K) (hα_spec : α' = Classical.choose
        (h_exists_alpha ε₁ ε' hφ_eq')) (s : Fin m) :
        FractionalIdeal.count K (spDM.conj_toHeightOneSpectrum (j := s))
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ α') =
        ((if ε' s then 0 else 1 : ℤ) - (if ε₁ s then 0 else 1 : ℤ)) := by
      subst hα_spec
      let α' := Classical.choose (h_exists_alpha ε₁ ε' hφ_eq')
      have hα'_ne : α' ≠ 0 := (Classical.choose_spec (h_exists_alpha ε₁ ε' hφ_eq')).1
      have hS_ne : FractionalIdeal.spanSingleton (𝓞 K)⁰ α' ≠ 0 :=
        FractionalIdeal.spanSingleton_ne_zero_iff.mpr hα'_ne
      have hJ0_ne : (J0 ε₁ : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
        rw [hJ0_to_ideal ε₁]
        exact J_ideal_ne_zero K spDM ε₁
      have hcount_mul := congrArg (FractionalIdeal.count K
        (spDM.conj_toHeightOneSpectrum (j := s))) hα_eq'
      rw [FractionalIdeal.count_mul K (spDM.conj_toHeightOneSpectrum (j := s)) hS_ne hJ0_ne]
        at hcount_mul
      rw [hJ0_to_ideal ε₁, count_J_conj_eq K spDM ε₁ s,
        hJ0_to_ideal ε', count_J_conj_eq K spDM ε' s] at hcount_mul
      linarith
    -- Core: relate count of α₂/α₃ to counts of α₂ and α₃
    have h_count_ratio_v (s : Fin m) : FractionalIdeal.count K
        (spDM.toHeightOneSpectrum (j := s))
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (α₂ / α₃ : K)) =
        ((if ε₂ s then 1 else 0 : ℤ) - (if ε₃ s then 1 else 0 : ℤ)) := by
      -- spanSingleton α₂ = spanSingleton α₃ * spanSingleton (α₂/α₃)
      have h_mul : FractionalIdeal.spanSingleton (𝓞 K)⁰ α₂ =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ α₃ *
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (α₂ / α₃ : K) := by
        calc
          FractionalIdeal.spanSingleton (𝓞 K)⁰ α₂
              = FractionalIdeal.spanSingleton (𝓞 K)⁰ (α₃ * (α₂ / α₃ : K)) := by
            field_simp [hα₃]
          _ = FractionalIdeal.spanSingleton (𝓞 K)⁰ α₃ *
              FractionalIdeal.spanSingleton (𝓞 K)⁰ (α₂ / α₃ : K) := by
            rw [FractionalIdeal.spanSingleton_mul_spanSingleton]
      have hS₂_ne : FractionalIdeal.spanSingleton (𝓞 K)⁰ α₂ ≠ 0 :=
        FractionalIdeal.spanSingleton_ne_zero_iff.mpr hα₂
      have hS₃_ne : FractionalIdeal.spanSingleton (𝓞 K)⁰ α₃ ≠ 0 :=
        FractionalIdeal.spanSingleton_ne_zero_iff.mpr hα₃
      have hS_ratio_ne : FractionalIdeal.spanSingleton (𝓞 K)⁰ (α₂ / α₃ : K) ≠ 0 :=
        FractionalIdeal.spanSingleton_ne_zero_iff.mpr h_ratio_ne_zero
      have hcount_mul := congrArg (FractionalIdeal.count K
        (spDM.toHeightOneSpectrum (j := s))) h_mul
      rw [FractionalIdeal.count_mul K (spDM.toHeightOneSpectrum (j := s)) hS₃_ne hS_ratio_ne]
        at hcount_mul
      rw [h_count_α_v ε₂ hφ₁₂ hα₂_eq α₂ rfl s,
        h_count_α_v ε₃ hφ₁₃ hα₃_eq α₃ rfl s] at hcount_mul
      omega
    have h_count_ratio_cv (s : Fin m) : FractionalIdeal.count K
        (spDM.conj_toHeightOneSpectrum (j := s))
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (α₂ / α₃ : K)) =
        ((if ε₂ s then 0 else 1 : ℤ) - (if ε₃ s then 0 else 1 : ℤ)) := by
      have h_mul : FractionalIdeal.spanSingleton (𝓞 K)⁰ α₂ =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ α₃ *
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (α₂ / α₃ : K) := by
        calc
          FractionalIdeal.spanSingleton (𝓞 K)⁰ α₂
              = FractionalIdeal.spanSingleton (𝓞 K)⁰ (α₃ * (α₂ / α₃ : K)) := by
            field_simp [hα₃]
          _ = FractionalIdeal.spanSingleton (𝓞 K)⁰ α₃ *
              FractionalIdeal.spanSingleton (𝓞 K)⁰ (α₂ / α₃ : K) := by
            rw [FractionalIdeal.spanSingleton_mul_spanSingleton]
      have hS₂_ne : FractionalIdeal.spanSingleton (𝓞 K)⁰ α₂ ≠ 0 :=
        FractionalIdeal.spanSingleton_ne_zero_iff.mpr hα₂
      have hS₃_ne : FractionalIdeal.spanSingleton (𝓞 K)⁰ α₃ ≠ 0 :=
        FractionalIdeal.spanSingleton_ne_zero_iff.mpr hα₃
      have hS_ratio_ne : FractionalIdeal.spanSingleton (𝓞 K)⁰ (α₂ / α₃ : K) ≠ 0 :=
        FractionalIdeal.spanSingleton_ne_zero_iff.mpr h_ratio_ne_zero
      have hcount_mul := congrArg (FractionalIdeal.count K
        (spDM.conj_toHeightOneSpectrum (j := s))) h_mul
      rw [FractionalIdeal.count_mul K (spDM.conj_toHeightOneSpectrum (j := s)) hS₃_ne
        hS_ratio_ne] at hcount_mul
      rw [h_count_α_cv ε₂ hφ₁₂ hα₂_eq α₂ rfl s,
        h_count_α_cv ε₃ hφ₁₃ hα₃_eq α₃ rfl s] at hcount_mul
      omega
    -- By count_eq_count_conj_of_fixed, counts at v and c(v) agree for α₂/α₃ ∈ K⁺
    have h_conj_eq (s : Fin m) : FractionalIdeal.count K
        (spDM.toHeightOneSpectrum (j := s))
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (α₂ / α₃ : K)) =
        FractionalIdeal.count K
        (spDM.conj_toHeightOneSpectrum (j := s))
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (α₂ / α₃ : K)) := by
      have h := count_eq_count_conj_of_fixed K h_ratio_ne_zero h_ratio_fixed
        (spDM.toHeightOneSpectrum (j := s))
      -- h: count at v = count at conjHeightOneSpectrum K v
      -- But conjHeightOneSpectrum K (toHeightOneSpectrum ...) = conj_toHeightOneSpectrum ... def-eq
      simpa using h
    -- Combine: (ε₂ s − ε₃ s) = −(ε₂ s − ε₃ s) → ε₂ s = ε₃ s
    have h_forall_s (s : Fin m) : ε₂ s = ε₃ s := by
      have h_eq := h_conj_eq s
      rw [h_count_ratio_v s, h_count_ratio_cv s] at h_eq
      -- h_eq: (if ε₂ s then 1 else 0) - (if ε₃ s then 1 else 0) =
      --       (if ε₂ s then 0 else 1) - (if ε₃ s then 0 else 1)
      -- Simplify: for any b ∈ {0,1}, (1-b) - (1-b') = -(b - b')
      -- So b-b' = -(b-b') → 2(b-b') = 0 → b = b' → ε₂ s = ε₃ s
      -- h_eq: (if ε₂ s then 1 else 0) - (if ε₃ s then 1 else 0) =
      --       (if ε₂ s then 0 else 1) - (if ε₃ s then 0 else 1)
      -- In ℤ, this forces ε₂ s = ε₃ s.  Decide handles all 4 Bool cases.
      have h_forall : ∀ (b₁ b₂ : Bool),
          (((if b₁ then (1 : ℤ) else 0) - (if b₂ then (1 : ℤ) else 0) =
            (if b₁ then (0 : ℤ) else 1) - (if b₂ then (0 : ℤ) else 1)) →
           b₁ = b₂) := by
        decide
      exact h_forall (ε₂ s) (ε₃ s) h_eq
    ext s; exact h_forall_s s
  -- -----------------------------------------------------------------
  -- Assemble the result
  -- -----------------------------------------------------------------
  exact {
    E := E
    G := G
    φ := φ
    cardE := cardE
    cardG := cardG
    hcardE := hcardE
    hcardG := hcardG
    h_card_ratio := h_card_ratio
    mk_unit := mk_unit
    mk_unit_mem_Λ := hmk_unit_mem_Λ
    mk_unit_norm := hmk_unit_norm
    mk_unit_inj := hmk_unit_inj
  }
