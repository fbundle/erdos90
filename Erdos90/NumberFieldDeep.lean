import Mathlib
import Erdos90.Defs
import Erdos90.Arithmetic

open Real Filter NumberField Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal Topology Complex Pointwise

noncomputable section

/-!
# Deep Number-Theoretic Components

This file factors the proof of `prop_3_2_to_3_6` and `prop_2_2` from
`NumberField.lean` into:

1. **Provable helpers** — pure analysis, no sorry.
2. **Pigeonhole lemma** (`exists_fiber_ge_div`, §3) — fully proved.
   The standard averaging argument: for f : α → β between finite nonempty types,
   ∃ b with |f⁻¹(b)| ≥ |α|/|β|.  This is the pure combinatorial core of Prop 2.2.
3. **Golod–Shafarevich tower** (`GSBaseData`, `gs_base_construction` + `gs_tower_levels`, §2) —
   two sorries for Props 3.2–3.5 and Prop 3.6 + type bridge, cleanly assembled
   into `golod_shafarevich_tower_with_lattice` → `GSTowerData`.
4. **CM class-group data** (`exists_cm_class_group_data`, §5) — one sorry for
   the algebraic number theory input to Prop 2.2: CM field K_j, split-prime
   ideal pairs, ClassGroup bound, norm-1 element constructor.
5. **Assembly** — `cm_norm_one_elements` (§6, proved modulo §5) and
   `prop_3_2_to_3_6_via_deep` (§7, proved modulo §2, §5).

The three sorries correspond to:
- §2: Golod–Shafarevich base construction (Props 3.2–3.5)
- §2: Chebotarev + Minkowski type bridge (Prop 3.6 + lattice)
- §5: CM field + class-group pigeonhole (Prop 2.2)

§4 contains four fully proved CM lemmas:
- `norm_div_star_eq_one` — pure complex analysis: ‖z / star z‖ = 1
- `cm_norm_div_conj_eq_one` — ‖φ(α / c(α))‖ = 1 at each complex embedding φ
- `normAtPlace_mixedEmbedding_cm_div_conj_eq_one` — normAtPlace = 1 at every
  infinite place under `mixedEmbedding`
- `mixedEmbedding_cm_div_conj_complex_norm_one` — concrete ‖.2 w‖ = 1 for
  each complex place
All use only the `IsCMField` API already in Mathlib v4.29.1.
-/

/-! ## §1  Analytic helpers (all proved) -/

/-- For ℓ ≥ 2, log(2ℓ) ≤ ℓ · log ℓ. -/
lemma log_two_mul_le (ℓ : ℕ) (hℓ : ℓ ≥ 2) :
    Real.log (2 * (ℓ : ℝ)) ≤ (ℓ : ℝ) * Real.log (ℓ : ℝ) := by
  have hℓ_pos : (0 : ℝ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hℓ_ge2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hlogℓ_ge_log2 : Real.log 2 ≤ Real.log ℓ :=
    Real.log_le_log (by norm_num) hℓ_ge2
  have hlogℓ_pos : Real.log ℓ > 0 :=
    lt_of_lt_of_le (Real.log_pos (by norm_num)) hlogℓ_ge_log2
  rw [Real.log_mul (by norm_num) hℓ_pos.ne']
  have hℓ1_ge1 : (ℓ : ℝ) - 1 ≥ 1 := by linarith
  have hlog2_le : Real.log 2 ≤ (ℓ - 1) * Real.log ℓ :=
    calc Real.log 2 ≤ Real.log ℓ := hlogℓ_ge_log2
      _ = 1 * Real.log ℓ := (one_mul _).symm
      _ ≤ (ℓ - 1) * Real.log ℓ := by nlinarith
  linarith

/-- For ℓ ≥ 2, 2 * ℓ ≥ 1 (used to satisfy rd_F ≥ 1). -/
lemma two_mul_nat_ge_one (ℓ : ℕ) (hℓ : ℓ ≥ 2) : (1 : ℝ) ≤ 2 * (ℓ : ℝ) := by
  have : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  linarith

/-! ## §2  Golod–Shafarevich tower — `GSTowerData` structure + constructor

The `GSTowerData` structure abstracts the output of Props 3.2–3.6:
- Fields `D₀`, `rd_F`, log bound, and `getTowerLevel` (an ∀M callback)
- `GSBaseData` packages Props 3.2–3.5 (D₀, rd_F, log bound)
- `gs_base_construction` — one sorry (Props 3.2–3.5)
- `gs_tower_levels` — one sorry (Prop 3.6 + Minkowski type bridge)
- `golod_shafarevich_tower_with_lattice` — assembly (no additional sorry)

See the `GSTowerData` docstring for full mathematical details.
-/

/-- Base data from Props 3.2–3.5: Golod–Shafarevich construction of D₀ = Q² and
    rd_F = |D_F|^{1/3} with log bound, extracted as a separate `def` to avoid
    `∃`-elimination into `Type` (since `GSTowerData` contains ℝ fields). -/
structure GSBaseData (ℓ : ℕ) where
  D₀ : ℝ
  hD₀_pos : D₀ > 0
  rd_F : ℝ
  hrd_F_ge1 : rd_F ≥ 1
  hlog_rd : Real.log rd_F ≤ (ℓ : ℝ) * Real.log (ℓ : ℝ)

/-- **Props 3.2–3.5**: Golod–Shafarevich base construction (sorry'd).

    For each ℓ ≥ 2, constructs:
    - ℓ primes r₁,…,r_ℓ ≡ 1 (mod 3) → cyclic cubic field F
    - M/F everywhere unramified, d(G) ≥ ℓ−1 for G = Gal(F^{ur,3}/F)
    - |D_F| = (∏ rᵢ)² = D², so rd_F = |D_F|^{1/3} ≤ 2ℓ
    - Chebotarev gives t = ⌊(ℓ−1)²/100⌋ primes q₁,…,qₜ
    - D₀ = Q² where Q = ∏ qᵦ

    Requires: Golod–Shafarevich pro-3 group theory, Shafarevich bound,
    Frattini quotient — none of this is in Mathlib v4.29.1. -/
def gs_base_construction (ℓ : ℕ) (hℓ : ℓ ≥ 2) : GSBaseData ℓ := by
  sorry

/-- **Prop 3.6 + Minkowski type bridge**: tower levels with lattice (sorry'd).

    Given the base data (D₀, rd_F) from Props 3.2–3.5, for each M returns a
    tower level Kⱼ = Fⱼ(i) with degree f ≥ M and Minkowski lattice
    Λ = Φⱼ(D₀⁻¹·𝒪_{Kⱼ}) ⊂ ℂ^f.

    Requires:
    - Quantitative Chebotarev: build infinite tower from G̅
    - Type bridge: `mixedSpace Kⱼ ≃ Fin f → ℂ` for totally complex CM field Kⱼ
    - Transport of `integerLattice` + `IsAddFundamentalDomain` across isomorphism
    - D₀-separation from split-prime product formula

    None of this is in Mathlib v4.29.1. -/
def gs_tower_levels (ℓ : ℕ) (hℓ : ℓ ≥ 2) (base : GSBaseData ℓ) (M : ℕ) :
    ∃ (f : ℕ), f ≥ M ∧ ∃ (hf1 : f ≥ 1) (Λ : AddSubgroup (Fin f → ℂ))
      (_ : Countable Λ) (F : Set (Fin f → ℂ)),
      IsAddFundamentalDomain Λ F volume ∧ volume F < ∞ ∧
      (∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf1)‖ ≥ base.D₀⁻¹) := by
  sorry


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
  /-- For any M, provides a tower level with degree f ≥ M and Minkowski lattice Λ ⊂ ℂ^f
      such that ‖v(fin0 hf1)‖ ≥ D₀⁻¹ for all nonzero v ∈ Λ.
      Encapsulates Prop 3.6 (Chebotarev split primes) + the Minkowski embedding type bridge. -/
  getTowerLevel (M : ℕ) : ∃ (f : ℕ), f ≥ M ∧ ∃ (hf1 : f ≥ 1) (Λ : AddSubgroup (Fin f → ℂ))
    (_ : Countable Λ) (F : Set (Fin f → ℂ)),
    IsAddFundamentalDomain Λ F volume ∧ volume F < ∞ ∧
    (∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf1)‖ ≥ D₀⁻¹)

/-- **Golod–Shafarevich tower with lattice** (Props 3.2–3.6).

    Assembly of `gs_base_construction` (Props 3.2–3.5, sorry'd) and
    `gs_tower_levels` (Prop 3.6 + type bridge, sorry'd) into `GSTowerData`.
    No additional sorries beyond the two sub-defs. -/
def golod_shafarevich_tower_with_lattice (ℓ : ℕ) (hℓ : ℓ ≥ 2) : GSTowerData ℓ :=
  let base := gs_base_construction ℓ hℓ
  { D₀ := base.D₀
    hD₀_pos := base.hD₀_pos
    rd_F := base.rd_F
    hrd_F_ge1 := base.hrd_F_ge1
    hlog_rd := base.hlog_rd
    getTowerLevel := gs_tower_levels ℓ hℓ base }

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

/-! ## §5  CM class-group data structure

    The structure `CMClassGroupData` abstracts the algebraic number theory
    input needed for Proposition 2.2 (class-group pigeonhole → norm-one set).

    The norm-1 property is already proved as `cm_norm_div_conj_eq_one` above.
    What remains (all sorry'd) is the constructive number theory:
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
  -- All fields require CM field / algebraic number theory not in Mathlib v4.29.1.
  exact {
    E := Fin 1
    G := Fin 1
    φ := sorry
    cardE := 1
    cardG := 1
    hcardE := sorry
    hcardG := sorry
    h_card_ratio := sorry
    mk_unit := sorry
    mk_unit_mem_Λ := sorry
    mk_unit_norm := sorry
    mk_unit_inj := sorry
  }

/-! ## §6  Assembly: `cm_norm_one_elements` (Proposition 2.2)

    The proof follows the paper's §2.1:
    1. Get `CMClassGroupData` from `exists_cm_class_group_data` (the algebraic sorry).
    2. Apply `exists_fiber_ge_div` (pigeonhole, §3) to φ : E → G.
    3. Obtain a fiber F = φ⁻¹(g) with |F| ≥ |E|/|G| ≥ exp(γ·f) + 1.
    4. Pick an anchor ε₀ ∈ F.
    5. For each ε ∈ F \ {ε₀}, embed u := mk_unit ε₀ ε ∈ Λ with ‖u r‖ = 1.
    6. By injectivity of mk_unit on F, these are all distinct, so
       |U| = |F| − 1 ≥ exp(γ·f). -/

def cm_norm_one_elements
    (f : ℕ) (hf1 : f ≥ 1) (D₀ : ℝ) (hD₀ : D₀ > 0) (_rd_F : ℝ)
    (t log_H : ℝ) (ht : t ≥ 0) (hγ_pos : t * Real.log 2 - log_H > 0)
    (Λ : AddSubgroup (Fin f → ℂ))
    (hΛ_sep : ∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf1)‖ ≥ D₀⁻¹) :
    ∃ (U : Finset (Fin f → ℂ)),
      (∀ u ∈ U, ∀ r : Fin f, ‖u r‖ = 1) ∧
      (∀ u ∈ U, (u : Fin f → ℂ) ∈ Λ) ∧
      ((U.card : ℝ) ≥ Real.exp ((t * Real.log 2 - log_H) * (f : ℝ))) := by
  -- Step 1: Get the CM class-group data (the one algebraic sorry)
  have data : CMClassGroupData f t log_H Λ :=
    exists_cm_class_group_data f hf1 D₀ hD₀ t log_H ht hγ_pos Λ hΛ_sep
  -- letI binds definitionally to the structure fields, avoiding haveI's opaque binder mismatch
  letI : Fintype data.E := data.fintypeE
  letI : DecidableEq data.E := data.decidableEqE
  letI : Fintype data.G := data.fintypeG
  letI : DecidableEq data.G := data.decidableEqG
  -- Convert h_card_ratio (uses ℕ cardE/cardG) to Fintype.card
  have h_card_ratio' : Real.exp ((t * Real.log 2 - log_H) * (f : ℝ)) + 1 ≤
      (Fintype.card data.E : ℝ) / (Fintype.card data.G : ℝ) := by
    simpa [data.hcardE, data.hcardG] using data.h_card_ratio
  -- Step 2: Prove G is nonempty (otherwise division by zero contradicts h_card_ratio)
  have hG_nonempty : 0 < Fintype.card data.G := by
    by_contra! hzero
    have hcard0 : Fintype.card data.G = 0 := by omega
    have hcard0' : (Fintype.card data.G : ℝ) = 0 := by exact_mod_cast hcard0
    have h_contra : Real.exp ((t * Real.log 2 - log_H) * (f : ℝ)) + 1 ≤ (0 : ℝ) := by
      simpa [hcard0'] using h_card_ratio'
    have h_exp_pos : Real.exp ((t * Real.log 2 - log_H) * (f : ℝ)) > 0 := Real.exp_pos _
    linarith
  -- Step 3: Apply the pigeonhole lemma to φ : E → G
  obtain ⟨g, hg⟩ := exists_fiber_ge_div data.φ hG_nonempty
  -- Fiber F = φ⁻¹(g)
  let F : Finset data.E := Finset.filter (λ ε => data.φ ε = g) Finset.univ
  have hF_mem (ε : data.E) (hε : ε ∈ F) : data.φ ε = g :=
    (Finset.mem_filter.mp hε).2
  -- Step 4: Size bound on F: |F| ≥ exp(γ·f) + 1
  have hF_size : (F.card : ℝ) ≥ Real.exp ((t * Real.log 2 - log_H) * (f : ℝ)) + 1 := by
    linarith
  -- F is nonempty (in fact |F| ≥ 2 since exp(γ·f) > 0)
  have hF_nonempty : F.Nonempty := by
    have h_exp_ge_one : Real.exp ((t * Real.log 2 - log_H) * (f : ℝ)) ≥ 1 := by
      have hγf_nonneg : 0 ≤ (t * Real.log 2 - log_H) * (f : ℝ) :=
        mul_nonneg (le_of_lt hγ_pos) (Nat.cast_nonneg _)
      exact Real.one_le_exp_iff.mpr hγf_nonneg
    have hcard_one : (1 : ℝ) ≤ F.card := by linarith
    have : 1 ≤ F.card := by exact_mod_cast hcard_one
    exact Finset.one_le_card.mp this
  obtain ⟨ε₀, hε₀⟩ := hF_nonempty
  have hε₀_fib : data.φ ε₀ = g := hF_mem ε₀ hε₀
  -- For Nat.cast_sub later: F.card ≥ 1
  have hF_card_ge_one : 1 ≤ F.card := by
    have : (1 : ℝ) ≤ F.card := by
      have h_exp_pos : Real.exp ((t * Real.log 2 - log_H) * (f : ℝ)) > 0 := Real.exp_pos _
      linarith
    exact_mod_cast this
  -- Step 5: Construct U = {mk_unit ε₀ ε | ε ∈ F \ {ε₀}}
  let F' : Finset data.E := F.erase ε₀
  have hF'_card : F'.card = F.card - 1 := by
    rw [Finset.card_erase_of_mem hε₀]
  -- The function ε ↦ mk_unit ε₀ ε is injective on F' (by mk_unit_inj)
  have h_inj_on : ∀ x ∈ F', ∀ y ∈ F',
      (λ ε => data.mk_unit ε₀ ε) x = (λ ε => data.mk_unit ε₀ ε) y → x = y := by
    intro x hx y hy h_eq
    have mem_x := Finset.mem_erase.mp hx
    have mem_y := Finset.mem_erase.mp hy
    have hx_fib : data.φ ε₀ = data.φ x := (hε₀_fib.trans (hF_mem x mem_x.2).symm)
    have hy_fib : data.φ ε₀ = data.φ y := (hε₀_fib.trans (hF_mem y mem_y.2).symm)
    exact data.mk_unit_inj ε₀ x y (Ne.symm mem_x.1) (Ne.symm mem_y.1) hx_fib hy_fib h_eq
  let U : Finset (Fin f → ℂ) := F'.image (λ ε => data.mk_unit ε₀ ε)
  have hU_card : U.card = F'.card :=
    Finset.card_image_of_injOn h_inj_on
  -- Step 6: Verify the three required properties of U
  have hU_norm : ∀ u ∈ U, ∀ r : Fin f, ‖u r‖ = 1 := by
    intro u hu r
    obtain ⟨ε, hε, rfl⟩ := Finset.mem_image.mp hu
    have mem_ε := Finset.mem_erase.mp hε
    have hε_fib : data.φ ε₀ = data.φ ε := (hε₀_fib.trans (hF_mem ε mem_ε.2).symm)
    exact data.mk_unit_norm ε₀ ε (Ne.symm mem_ε.1) hε_fib r
  have hU_mem_Λ : ∀ u ∈ U, u ∈ Λ := by
    intro u hu
    obtain ⟨ε, hε, rfl⟩ := Finset.mem_image.mp hu
    have mem_ε := Finset.mem_erase.mp hε
    have hε_fib : data.φ ε₀ = data.φ ε := (hε₀_fib.trans (hF_mem ε mem_ε.2).symm)
    exact data.mk_unit_mem_Λ ε₀ ε (Ne.symm mem_ε.1) hε_fib
  have hU_size : (U.card : ℝ) ≥ Real.exp ((t * Real.log 2 - log_H) * (f : ℝ)) := by
    rw [hU_card, hF'_card]
    rw [Nat.cast_sub hF_card_ge_one, Nat.cast_one]
    linarith
  exact ⟨U, hU_norm, hU_mem_Λ, hU_size⟩

/-! ## §7  Assembly of `prop_3_2_to_3_6` -/

/-- **Structured proof of `prop_3_2_to_3_6`** (assembly only; no new sorry).

    Chains `golod_shafarevich_tower_with_lattice` (§2, returns `GSTowerData`,
    two sorries) and `cm_norm_one_elements` (§6, one sorry) together.  The log bound
    (log rd_F ≤ C_rd·ℓ·log ℓ for C_rd = 1) is fully proved via `log_two_mul_le`.

    The caller (`exists_admissible_family` in NumberField.lean) computes
    t and log_H from the tower's ℓ and rd_F, uses `prop_p6` to prove γ > 0,
    and calls `cm_norm_one_elements` to get U.  This keeps the analytic
    P6 proof (fully proved) separate from the algebraic sorry. -/
theorem prop_3_2_to_3_6_via_deep :
    ∃ (C_rd : ℝ), C_rd > 0 ∧
    ∀ (ℓ : ℕ), ℓ ≥ 2 →
    ∃ (D₀ : ℝ), D₀ > 0 ∧ ∃ (rd_F : ℝ), rd_F ≥ 1 ∧
      Real.log rd_F ≤ C_rd * (ℓ : ℝ) * Real.log (ℓ : ℝ) ∧
      ∀ (M : ℕ),
      ∃ (f : ℕ), f ≥ M ∧ ∃ (hf1 : f ≥ 1) (Λ : AddSubgroup (Fin f → ℂ))
        (_ : Countable Λ) (F : Set (Fin f → ℂ)),
        IsAddFundamentalDomain Λ F volume ∧ volume F < ∞ ∧
        (∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf1)‖ ≥ D₀⁻¹) ∧
        ∀ (t log_H : ℝ), t ≥ 0 → (t * Real.log 2 - log_H > 0) →
        ∃ (U : Finset (Fin f → ℂ)),
          (∀ u ∈ U, ∀ r : Fin f, ‖u r‖ = 1) ∧
          (∀ u ∈ U, (u : Fin f → ℂ) ∈ Λ) ∧
          ((U.card : ℝ) ≥ Real.exp ((t * Real.log 2 - log_H) * (f : ℝ))) := by
  refine ⟨1, one_pos, fun ℓ hℓ => ?_⟩
  let tower : GSTowerData ℓ := golod_shafarevich_tower_with_lattice ℓ hℓ
  refine ⟨tower.D₀, tower.hD₀_pos, tower.rd_F, tower.hrd_F_ge1, by
    -- log rd_F ≤ ℓ·log ℓ, and C_rd = 1
    simpa using tower.hlog_rd, fun M => ?_⟩
  obtain ⟨f, hf_ge, hf1, Λ, hΛ_countable, F, hF_fund, hF_fin, hΛ_sep⟩ := tower.getTowerLevel M
  refine ⟨f, hf_ge, hf1, Λ, hΛ_countable, F, hF_fund, hF_fin, hΛ_sep, fun t log_H ht hγ_pos => ?_⟩
  exact cm_norm_one_elements f hf1 tower.D₀ tower.hD₀_pos tower.rd_F t log_H ht hγ_pos Λ hΛ_sep

end
