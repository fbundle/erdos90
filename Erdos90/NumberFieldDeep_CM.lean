import Mathlib
import Erdos90.Arithmetic

open Real Filter NumberField Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal Topology Complex Pointwise

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

/-- When K is totally complex of degree f (complex places), mixedSpace K is equivalent
to `Fin f → ℂ`.  This is the type bridge needed for `gs_tower_levels`. -/
def mixedSpace_equiv_pi_fin_of_card {K : Type*} [Field K] [NumberField K]
    (h_no_real : InfinitePlace.nrRealPlaces K = 0) (f : ℕ)
    (hf : InfinitePlace.nrComplexPlaces K = f) :
    mixedEmbedding.mixedSpace K ≃ₗ[ℝ] (Fin f → ℂ) := by
  classical
    let e₁ := mixedSpace_equiv_complex_places h_no_real
    -- Index equivalence from complex place subtype to Fin f
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
    let e_idx : {w : InfinitePlace K // InfinitePlace.IsComplex w} ≃ Fin f :=
      (Fintype.equivFin _).trans e_card
    -- Lift to arrow equivalence, then as a linear equivalence
    let e_arrow : ({w : InfinitePlace K // InfinitePlace.IsComplex w} → ℂ) ≃ (Fin f → ℂ) :=
      Equiv.arrowCongr e_idx (Equiv.refl ℂ)
    let e_pi : ({w : InfinitePlace K // InfinitePlace.IsComplex w} → ℂ) ≃ₗ[ℝ]
      (Fin f → ℂ) := {
        e_arrow with
        map_add' := fun x y => rfl
        map_smul' := fun r x => rfl
      }
    exact e₁.trans e_pi

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

/-- Abstract data packaging the CM field / class-group construction for Prop 2.2.

    Provides:
    - Finite types `E` (sign vectors {±1}^m) and `G` (abstracting the class group),
      with `Fintype`/`DecidableEq` as typeclass instances (auto-available from the
      structure fields).
    - A map `φ : E → G` (the class-group map)
    - A cardinality ratio `|E|/|G| ≥ exp(γ·f) + 1` (strong enough to absorb the −1
      loss when fixing an anchor element)
    - A function `mk_unit` that, given ε₁ ≠ ε₂ in the same fiber of φ, produces
      a vector in Λ ⊂ ℂ^f with all coordinates of modulus 1
    - Injectivity: fixing ε₁, the map ε₂ ↦ mk_unit ε₁ ε₂ is injective on the fiber

    **Reference**: Proposition 2.2 of [OpenAI 2026]; Neukirch Ch. I §6–7, Ch. III §3. -/
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
    (f : ℕ) (hf1 : f ≥ 1) (D₀ : ℝ) (hD₀ : D₀ > 0)
    (t log_H : ℝ) (ht : t ≥ 0) (hγ_pos : t * Real.log 2 - log_H > 0)
    (Λ : AddSubgroup (Fin f → ℂ))
    (hΛ_sep : ∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf1)‖ ≥ D₀⁻¹) :
    CMClassGroupData f t log_H Λ := by
  -- -----------------------------------------------------------------
  -- §5.1  Choose m = ⌈t·f⌉ sign bits (reference value; not used in the stub)
  --
  -- In the full proof (Prop 2.2), m = t·f is the number of split‑prime
  -- ideal pairs in K.  We record the bound m ≥ t·f for reference.
  -- -----------------------------------------------------------------
  set m : ℕ := ⌈t * (f : ℝ)⌉₊ with hm_def
  have hm_ge_tf : (t : ℝ) * (f : ℝ) ≤ (m : ℝ) := by
    rw [hm_def]
    have hceil : (t : ℝ) * (f : ℝ) ≤ (⌈(t : ℝ) * (f : ℝ)⌉₊ : ℝ) :=
      (Nat.ceil_le (a := (t : ℝ) * (f : ℝ)) (n := ⌈(t : ℝ) * (f : ℝ)⌉₊)).mp (le_refl _)
    simpa [hm_def] using hceil
  -- -----------------------------------------------------------------
  -- §5.2  Sign‑vector type E and class group G (placeholder)
  --
  -- In the full proof E = Fin(2^m) ≅ {±1}^m encodes choices of 𝔓_s vs c𝔓_s
  -- for each split‑prime pair.  For the stub we set |E| = cardE where
  -- cardE := ⌈exp(γ·f)⌉₊ + 2, which guarantees |E|/|G| ≥ exp(γ·f) + 1
  -- (with cardinality to spare for the anchor element).
  --
  -- G = Fin 1 is a placeholder for ClassGroup(𝒪_K).
  -- -----------------------------------------------------------------
  let cardE : ℕ := ⌈Real.exp ((t * Real.log 2 - log_H) * (f : ℝ))⌉₊ + 2
  have hcardE_pos : cardE > 0 := by
    refine Nat.succ_pos _
  let E : Type := Fin cardE
  letI : Fintype E := inferInstance
  letI : DecidableEq E := inferInstance
  have hcardE : cardE = Fintype.card E := by dsimp [cardE, E]; simp
  let G : Type := Fin 1
  letI : Fintype G := inferInstance
  letI : DecidableEq G := inferInstance
  let cardG : ℕ := 1
  have hcardG : cardG = Fintype.card G := by dsimp [cardG, G]; simp
  -- -----------------------------------------------------------------
  -- §5.3  The class‑group map φ : E → G (constant for the stub)
  -- -----------------------------------------------------------------
  let φ : E → G := fun _ => ⟨0, by decide⟩
  -- -----------------------------------------------------------------
  -- §5.4  Cardinality ratio |E|/|G| ≥ exp(γ·f) + 1
  --
  -- With |E| = ⌈exp(γ·f)⌉ + 2 and |G| = 1:
  --   (cardE : ℝ) = ⌈exp(γ·f)⌉ + 2 ≥ exp(γ·f) + 2 > exp(γ·f) + 1.
  --
  -- This requires no additional hypotheses on log_H, t, or f.
  -- -----------------------------------------------------------------
  have h_card_ratio : Real.exp ((t * Real.log 2 - log_H) * (f : ℝ)) + 1 ≤
      (cardE : ℝ) / (cardG : ℝ) := by
    have hcardG_one : (cardG : ℝ) = 1 := by dsimp [cardG, G]; simp
    rw [hcardG_one, div_one]
    -- We need: exp(γ·f) + 1 ≤ cardE = ⌈exp(γ·f)⌉₊ + 2
    -- From Nat.ceil: exp(γ·f) ≤ ⌈exp(γ·f)⌉₊
    -- Then exp(γ·f) + 1 ≤ ⌈exp(γ·f)⌉₊ + 1 ≤ ⌈exp(γ·f)⌉₊ + 2 = cardE
    have hceil : (Real.exp ((t * Real.log 2 - log_H) * (f : ℝ)) : ℝ) ≤
        (⌈Real.exp ((t * Real.log 2 - log_H) * (f : ℝ))⌉₊ : ℝ) :=
      (Nat.ceil_le (a := Real.exp ((t * Real.log 2 - log_H) * (f : ℝ)))
        (n := ⌈Real.exp ((t * Real.log 2 - log_H) * (f : ℝ))⌉₊)).mp (le_refl _)
    -- exp ≤ ⌈exp⌉, so exp + 1 ≤ ⌈exp⌉ + 1 ≤ ⌈exp⌉ + 2 = (cardE : ℝ)
    -- (cardE : ℝ) = (⌈exp⌉₊ + 2 : ℝ) = (⌈exp⌉₊ : ℝ) + 2 by Nat.cast_add
    have htemp : (Real.exp ((t * Real.log 2 - log_H) * (f : ℝ)) + 1 : ℝ) ≤
        ((⌈Real.exp ((t * Real.log 2 - log_H) * (f : ℝ))⌉₊ : ℝ) + 2) := by
      linarith
    simpa [cardE, Nat.cast_add] using htemp
  -- -----------------------------------------------------------------
  -- §5.6  The mk_unit constructor
  --
  -- Mathematical construction (paper §2.1):
  --   For ε₁ ≠ ε₂ with φ(ε₁) = φ(ε₂), the ideal 𝔄_{ε₂} · 𝔄_{ε₁}⁻¹
  --   is principal.  Choose a generator α ∈ K× (axiom of choice).
  --   Then mk_unit ε₁ ε₂ = Φ(α / c(α)), where:
  --     • Φ : K → Fin f → ℂ is the Minkowski embedding
  --       (f distinct complex embeddings, one from each conjugate pair)
  --     • c : K → K is complex conjugation (IsCMField.complexConj)
  --     • α / c(α) has norm 1 in every embedding (proved in §4)
  --     • Q²·α/c(α) ∈ 𝒪_K (valuation argument), so α/c(α) ∈ D₀⁻¹·𝒪_K
  --       hence mk_unit ε₁ ε₂ ∈ Λ  (since Λ = Φ(D₀⁻¹·𝒪_K))
  --
  -- The norm‑1 property (§4 lemmas) and the injectivity argument
  -- (valuations at 𝔓_s distinguish the u_ε) are both mathematically
  -- sound but require the split‑prime API and CM‑field API not
  -- currently in Mathlib v4.29.1.
  -- -----------------------------------------------------------------
  let mk_unit : E → E → Fin f → ℂ :=
    fun ε₁ ε₂ => (0 : Fin f → ℂ)  -- placeholder zero vector
  have hmk_unit_mem_Λ : ∀ ε₁ ε₂, ε₁ ≠ ε₂ → φ ε₁ = φ ε₂ → mk_unit ε₁ ε₂ ∈ Λ := by
    intro ε₁ ε₂ _hne _heq
    -- 0 ∈ Λ because Λ is an AddSubgroup (contains zero)
    exact AddSubgroup.zero_mem Λ
  have hmk_unit_norm : ∀ ε₁ ε₂, ε₁ ≠ ε₂ → φ ε₁ = φ ε₂ → ∀ r, ‖mk_unit ε₁ ε₂ r‖ = 1 := by
    -- GAP: Placeholder mk_unit = 0 has ‖0‖ = 0 ≠ 1, so this cannot be proved.
    -- The real proof: given ε₁ ≠ ε₂ with φ(ε₁) = φ(ε₂) (same ideal class),
    -- the principal ideal 𝔄_{ε₂}·𝔄_{ε₁}⁻¹ = (α) for some α ∈ K^×.
    -- Define mk_unit ε₁ ε₂ := Φ(α / c(α)) where:
    --   • Φ : K → Fin f → ℂ is the Minkowski embedding (cmMinkowskiEquiv)
    --   • c = IsCMField.complexConj : K → K is complex conjugation
    -- Then for each coordinate r (corresponding to a complex embedding σ_r):
    --   ‖mk_unit ε₁ ε₂ r‖ = ‖σ_r(α / c(α))‖ = ‖σ_r(α) / star(σ_r(α))‖ = 1
    -- by §4 lemma `cm_norm_div_conj_eq_one` (proved at line ~220 of this file).
    -- WHAT'S MISSING: the CM field K, the ideal generators α, and the
    -- connection between Φ and the complex embeddings (IsCMField API).
    sorry
  have hmk_unit_inj : ∀ ε₁ ε₂ ε₃, ε₁ ≠ ε₂ → ε₁ ≠ ε₃ → φ ε₁ = φ ε₂ → φ ε₁ = φ ε₃ →
      mk_unit ε₁ ε₂ = mk_unit ε₁ ε₃ → ε₂ = ε₃ := by
    -- GAP: Placeholder mk_unit = 0 is constant, so injectivity fails.
    -- The real proof (with mk_unit ε₁ ε₂ = Φ(α₂ / c(α₂))):
    --   Φ(α₂/c(α₂)) = Φ(α₃/c(α₃))
    --   → α₂/c(α₂) = α₃/c(α₃)  (Φ is injective on K)
    --   → α₂·c(α₃) = α₃·c(α₂)
    --   → (α₂/α₃) = c(α₂/α₃)
    --   → α₂/α₃ ∈ K⁺ (the totally real subfield)
    --   → v_𝔓(α₂/α₃) ∈ 2ℤ  (valuation parity from CM split‑prime condition)
    --   → the sign-vector entries for ε₂, ε₃ encode these valuations mod 2
    --   → ε₂ = ε₃
    -- WHAT'S MISSING: split‑prime ideal pairs in CM field, valuation parity
    -- `IsCMField.complexConj` API in Mathlib (exists but incomplete).
    sorry
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
