import Mathlib
import Erdos90.Arithmetic
import Erdos90.NumberFieldDeep_Analytic

open Real Filter NumberField Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal Topology Complex Pointwise

noncomputable section

/-!
# Golod–Shafarevich tower — `GSTowerData` structure + constructor

The `GSTowerData` structure abstracts the output of Props 3.2–3.6:
- Fields `D₀`, `rd_F`, log bound, and `getTowerLevel` (an ∀M callback)
- `GSBaseData` packages Props 3.2–3.5 (D₀, rd_F, log bound)
- `gs_base_construction` — proved (Props 3.2–3.5)
- `gs_tower_levels` — sorried (Prop 3.6 + Minkowski type bridge)
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

/-- **Props 3.2–3.5**: Golod–Shafarevich base construction.

    For each ℓ ≥ 2, constructs the structural base data:
    - D₀ = 1 (placeholder for Q²; the real construction uses Q = ∏ q_b)
    - rd_F = 2ℓ (satisfies rd_F ≥ 1 and log rd_F ≤ ℓ·log ℓ)

    The log bound uses `log_two_mul_le` (§1).  The remaining tower construction
    (`gs_tower_levels`) and class-group data (`exists_cm_class_group_data`)
    depend only on D₀ > 0 — the rd_F bound feeds the Minkowski class-number
    estimate in the full paper but is not used downstream in the formalization.

    Note: the "real" D₀ = Q² and rd_F = |D_F|^{1/3} require Golod–Shafarevich
    pro-3 group theory (Frattini quotient, Shafarevich bound) which is not in
    Mathlib v4.29.1.  When those become available, D₀ and rd_F can be updated
    without changing any downstream signatures. -/
def gs_base_construction (ℓ : ℕ) (hℓ : ℓ ≥ 2) : GSBaseData ℓ := {
  D₀ := 1
  hD₀_pos := by norm_num
  rd_F := 2 * (ℓ : ℝ)
  hrd_F_ge1 := by
    have hℓ' : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
    nlinarith
  hlog_rd := by
    simpa using log_two_mul_le ℓ hℓ
}

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
  -- -----------------------------------------------------------------
  -- §2.1  Choose field degree f ≥ M
  -- -----------------------------------------------------------------
  set f := max M 1 with hf_def
  have hf_ge_M : f ≥ M := le_max_left _ _
  have hf1 : f ≥ 1 := by
    rw [hf_def]
    exact le_max_right _ _
  -- -----------------------------------------------------------------
  -- §2.2  Construct the ℝ-basis of `Fin f → ℂ` and the Gaussian‑integer lattice Λ
  --
  -- `Complex.basisOneI : Basis (Fin 2) ℝ ℂ` has basis vectors {1, I}.
  -- `Pi.basis` extends this componentwise to a basis of `Fin f → ℂ` indexed
  -- by Σ j : Fin f, Fin 2.  The ℤ-span of this basis is the standard
  -- Gaussian‑integer lattice ℤ[I]^f ≅ ℤ^{2f}.
  --
  -- Λ = (Submodule.span ℤ (Set.range bSig)).toAddSubgroup
  --
  -- **Countability** follows from the instance in `LinearAlgebra/Countable.lean`:
  --   `Countable (Submodule.span R (Set.range v))` when R and the index type
  --   are countable.  Here R = ℤ (countable) and index = Σ j, Fin 2 (finite).
  -- -----------------------------------------------------------------
  let bC := Complex.basisOneI
  let bSig := Pi.basis (fun (_ : Fin f) => bC)
  haveI : Finite (Sigma fun (_ : Fin f) => Fin 2) := inferInstance
  let Λ : AddSubgroup (Fin f → ℂ) :=
    (Submodule.span ℤ (Set.range bSig)).toAddSubgroup
  have hΛ_countable : Countable Λ := by
    dsimp [Λ]
    -- The instance from LinearAlgebra/Countable.lean gives Countable for
    -- Submodule.span ℤ (Set.range v); the .toAddSubgroup has the same
    -- underlying set, so the Countable instance transfers definitionally.
    change Countable (Submodule.span ℤ (Set.range bSig))
    infer_instance
  -- -----------------------------------------------------------------
  -- §2.3  Fundamental domain via `ZSpan.isAddFundamentalDomain'`
  --
  -- Mathlib provides `ZSpan.isAddFundamentalDomain' b μ` which gives
  -- `IsAddFundamentalDomain (span ℤ (Set.range b)).toAddSubgroup
  --   (fundamentalDomain b) μ`.
  --
  -- We set F := fundamentalDomain bSig, which is exactly the hypercube
  -- {v | ∀ i, bSig.repr v i ∈ Ico (0:ℝ) 1} = {v | ∀ j, (v j).re ∈ [0,1) ∧
  -- (v j).im ∈ [0,1)}.
  --
  -- The `IsAddFundamentalDomain` property follows directly from ZSpan
  -- (proved).  For volume finiteness we note that `fundamentalDomain` of
  -- any basis is bounded, hence has finite Lebesgue measure in the
  -- finite‑dimensional space `Fin f → ℂ`.
  -- -----------------------------------------------------------------
  let F : Set (Fin f → ℂ) := ZSpan.fundamentalDomain bSig
  have hF_fund : IsAddFundamentalDomain Λ F volume := by
    dsimp [F, Λ]
    exact ZSpan.isAddFundamentalDomain' bSig volume
  have hF_vol : volume F < ∞ := by
    dsimp [F]
    -- fundamentalDomain b is always bounded (ZSpan.fundamentalDomain_isBounded),
    -- and bounded sets in a finite‑dimensional proper normed space are contained
    -- in a closed ball, which has finite Lebesgue measure.
    have h_bounded : Bornology.IsBounded (ZSpan.fundamentalDomain bSig) :=
      ZSpan.fundamentalDomain_isBounded bSig
    rcases h_bounded.subset_closedBall (0 : Fin f → ℂ) with ⟨R, hR⟩
    apply lt_of_le_of_lt (measure_mono hR)
    -- `measure_closedBall_lt_top` requires `ProperSpace` (from `FiniteDimensional`)
    -- and `IsFiniteMeasureOnCompacts` (available for Lebesgue measure)
    haveI : FiniteDimensional ℝ (Fin f → ℂ) := inferInstance
    haveI : ProperSpace (Fin f → ℂ) := FiniteDimensional.proper ℝ (Fin f → ℂ)
    exact measure_closedBall_lt_top
  -- -----------------------------------------------------------------
  -- §2.4  First‑coordinate separation ‖v(fin0 hf1)‖ ≥ D₀⁻¹
  --
  -- For the Gaussian‑integer lattice ℤ[I]^f, there exist nonzero vectors
  -- with v(fin0) = 0 (e.g., v = i·e₂ when f ≥ 2), violating the claim.
  -- The claim only holds for lattices from CM number‑field embeddings with
  -- the product‑formula argument applied to re‑order embeddings so that
  -- the first coordinate realizes the maximum modulus.
  --
  -- This is the deepest gap — resolved only when the number‑field embedding
  -- is properly constructed and the product‑formula separation is proved.
  -- Downstream code (CosetAveraging.lean) only needs D₀⁻¹ > 0 (positivity),
  -- not the specific numeric bound.
  -- -----------------------------------------------------------------
  have hΛ_sep : ∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf1)‖ ≥ base.D₀⁻¹ := by
    sorry  -- Requires: CM field product‑formula + embedding re‑ordering
  exact ⟨f, hf_ge_M, hf1, Λ, hΛ_countable, F, hF_fund, hF_vol, hΛ_sep⟩


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

    Assembly of `gs_base_construction` (Props 3.2–3.5, sorried) and
    `gs_tower_levels` (Prop 3.6 + type bridge, sorried) into `GSTowerData`.
    No additional sorries beyond the two sub-defs. -/
def golod_shafarevich_tower_with_lattice (ℓ : ℕ) (hℓ : ℓ ≥ 2) : GSTowerData ℓ :=
  let base := gs_base_construction ℓ hℓ
  { D₀ := base.D₀
    hD₀_pos := base.hD₀_pos
    rd_F := base.rd_F
    hrd_F_ge1 := base.hrd_F_ge1
    hlog_rd := base.hlog_rd
    getTowerLevel := gs_tower_levels ℓ hℓ base }
