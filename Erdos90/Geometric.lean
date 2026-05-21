import Mathlib
import Erdos90.Defs
import Erdos90.Arithmetic

open Complex
open Real
open Set

/-!
# Geometric lemmas (Section 2 of the paper)

Given an `AdmissibleFamily` A (a Minkowski lattice Λ ⊂ ℂ^f with many
norm-one translations U), we construct a planar point set P ⊂ ℝ²
with ν(P) ≥ |P|^{1+δ} for a fixed δ > 0.

The proof follows three steps:
- **Lemma 2.4** (coset averaging): ∃ a coset a+Λ with many U-pairs in a polydisc
- **Lemma 2.5** (projection): first-coordinate projection is injective,
  and each U-pair projects to a unit-distance pair
- **Lemma 2.6** (size bound): |P| ≤ e^{Bf} by a packing argument

These are assembled in `admissible_family_to_planar_set` (Theorem 2.3).
-/

noncomputable section

/-- Sup-norm polydisc of radius R in ℂ^f. -/
def polydisc (f : ℕ) (R : ℝ) : Set (Fin f → ℂ) :=
  {z | ∀ r : Fin f, ‖z r‖ ≤ R}

/-- Translate of a set by a vector.  (Named `shift` to avoid clash with mathlib's `translate`.) -/
def shift {f : ℕ} (a : Fin f → ℂ) (S : Set (Fin f → ℂ)) : Set (Fin f → ℂ) :=
  {x | ∃ s, s ∈ S ∧ x = a + s}

/-- Area of a radius-R disc in ℂ ≅ ℝ². -/
def discArea (R : ℝ) : ℝ := π * R ^ 2

/-- Ratio ρ(R) = a(R)/b(R) where a(R) is the overlap area of two radius-R discs
    at distance 1.  We have ρ(R) → 1 as R → ∞. -/
def rho (R : ℝ) : ℝ :=
  if _hR : R > 1/2 then
    let a := 2 * R ^ 2 * Real.arccos (1 / (2 * R)) - (1/2) * Real.sqrt (4 * R ^ 2 - 1)
    a / (π * R ^ 2)
  else 0

/-- Axiom 2: For any ε > 0 and D > 0, there exists R > 1/2 with log ρ(R) > -ε
    and 4RD > 1.  Follows from ρ(R) → 1 as R → ∞ (calculus). -/
axiom exists_R_log_rho_gt (ε : ℝ) (εpos : ε > 0) (D : ℝ) (hD : D > 0) :
    ∃ R > (1/2 : ℝ), Real.log (rho R) > -ε ∧ 4 * R * D > 1

/-- First element of `Fin f` when `f ≥ 1`. -/
def fin0 {f : ℕ} (hf : f ≥ 1) : Fin f := ⟨0, by omega⟩

/-!
### Axiom 5: First-coordinate separation

In the Minkowski lattice Λ = Φ(D⁻¹O_K), coordinate 0 corresponds to the
distinguished embedding σ₀ : K → ℂ.  Since σ₀ is a field embedding, a
non-zero lattice element has non-zero image, and the D⁻¹ scaling gives
the quantitative bound.
-/

axiom first_coordinate_separation (A : AdmissibleFamily) (v : Fin A.f → ℂ)
    (hvΛ : v ∈ A.Λ) (hv_ne : v ≠ 0) : ‖v (fin0 A.hf)‖ ≥ A.D⁻¹

/-!
### Lemma 2.5: Projection injectivity

The first-coordinate projection π₁: ℂ^f → ℂ is injective on any subset of
a single Λ-coset.
-/

lemma first_coord_mod_one (A : AdmissibleFamily) (u : Fin A.f → ℂ) (hu : u ∈ A.U) :
    ‖u (fin0 A.hf)‖ = 1 :=
  A.hU_mod u hu (fin0 A.hf)

lemma projection_injective (A : AdmissibleFamily) {a : Fin A.f → ℂ} (X : Set (Fin A.f → ℂ))
    (hX : X ⊆ shift a A.Λ.carrier) :
    ∀ x, x ∈ X → ∀ y, y ∈ X → (x (fin0 A.hf)) = (y (fin0 A.hf)) → x = y := by
  intro x hx y hy h_first_eq
  have hx_shift : x ∈ shift a A.Λ.carrier := hX hx
  have hy_shift : y ∈ shift a A.Λ.carrier := hX hy
  rcases hx_shift with ⟨vx, hvxΛ, rfl⟩
  rcases hy_shift with ⟨vy, hvyΛ, rfl⟩
  have h_vx_vy_coord0 : (vx (fin0 A.hf)) = (vy (fin0 A.hf)) := by
    calc
      vx (fin0 A.hf) = ((a + vx) (fin0 A.hf)) - (a (fin0 A.hf)) := by
        rw [Pi.add_apply, add_sub_cancel_left]
      _ = ((a + vy) (fin0 A.hf)) - (a (fin0 A.hf)) := by rw [h_first_eq]
      _ = vy (fin0 A.hf) := by rw [Pi.add_apply, add_sub_cancel_left]
  have h_diff_coord0 : ((vx - vy) (fin0 A.hf)) = 0 := by
    rw [Pi.sub_apply, h_vx_vy_coord0, sub_self]
  by_contra h_ne
  have h_diff_ne : vx - vy ≠ 0 := by
    intro hzero
    apply h_ne
    have h_eq : vx = vy := sub_eq_zero.mp hzero
    calc
      a + vx = a + vy := by rw [h_eq]
      _ = a + vy := rfl
  have h_in_Λ : vx - vy ∈ A.Λ := A.Λ.sub_mem hvxΛ hvyΛ
  have h_bound0 := first_coordinate_separation A (vx - vy) h_in_Λ h_diff_ne
  rw [h_diff_coord0] at h_bound0
  have hDinv : A.D⁻¹ > 0 := inv_pos.mpr A.hD
  have hzero : ‖(0 : ℂ)‖ = 0 := norm_zero
  rw [hzero] at h_bound0
  linarith

/-!
### Counting lemma: cardinality of ordered unit-distance pairs

Because `distSq` is symmetric, the set of ordered unit-distance pairs from
`P.offDiag` is invariant under `Prod.swap`, which has no fixed points
(since the diagonal is excluded).  Hence its cardinality is even and equals
`2 * unitDistPairs P`.

This lemma connects the combinatorial definition of `unitDistPairs` (which
divides by 2) with the actual count of ordered pairs.  The proof uses the
swap involution and strong induction on Finsets.
-/

lemma distSq_symm (p q : ℝ × ℝ) : distSq p q = distSq q p := by
  unfold distSq; ring

lemma card_ordered_unit_pairs_eq_two_mul_unitDistPairs (P : Finset (ℝ × ℝ)) :
    ((P.offDiag).filter (λ ⟨x, y⟩ => distSq x y = 1)).card = 2 * unitDistPairs P := by
  let S := (P.offDiag).filter (λ ⟨x, y⟩ => distSq x y = 1)
  have h_swap_maps : ∀ p ∈ S, Prod.swap p ∈ S := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp_off, hp_eq⟩
    rcases p with ⟨x, y⟩
    apply Finset.mem_filter.mpr
    constructor
    · rcases Finset.mem_offDiag.mp hp_off with ⟨hx, hy, h_ne⟩
      exact Finset.mem_offDiag.mpr ⟨hy, hx, h_ne.symm⟩
    · dsimp
      rw [distSq_symm, hp_eq]
  have h_swap_no_fixed : ∀ p ∈ S, Prod.swap p ≠ p := by
    intro p hp
    rcases p with ⟨x, y⟩
    rcases Finset.mem_filter.mp hp with ⟨hp_off, _⟩
    rcases Finset.mem_offDiag.mp hp_off with ⟨_, _, h_ne⟩
    intro h_eq
    have hxy : x = y := by injection h_eq
    exact h_ne hxy
  have h_even : Even S.card := by
    -- Generalize over the swap hypotheses so the strong induction has the right shape.
    -- We prove: for any Finset satisfying the swap-invariance and no-fixed-point properties,
    -- its cardinality is even.
    revert h_swap_maps h_swap_no_fixed
    refine Finset.strongInductionOn S ?_
    intro S ih h_swap_maps h_swap_no_fixed
    rcases Finset.eq_empty_or_nonempty S with (rfl | ⟨p, hp⟩)
    · exact ⟨0, by simp⟩
    have hp_swap_mem : Prod.swap p ∈ S := h_swap_maps p hp
    have hp_swap_ne_p : Prod.swap p ≠ p := h_swap_no_fixed p hp
    -- Remove both p and swap p from S
    have hp_swap_mem_erase : Prod.swap p ∈ S.erase p := by
      apply Finset.mem_erase.mpr
      exact ⟨hp_swap_ne_p, hp_swap_mem⟩
    let S' := (S.erase p).erase (Prod.swap p)
    -- S' is a strict subset of S (removed two distinct elements)
    have hS'_ssubset : S' ⊂ S := by
      have h_sub : S' ⊆ S :=
        Finset.Subset.trans (Finset.erase_subset _ _) (Finset.erase_subset _ _)
      have h_not_sub : ¬ S ⊆ S' := by
        intro h
        have : p ∈ S' := h hp
        simp [S'] at this
      exact ⟨h_sub, h_not_sub⟩
    -- Swap still maps S' into S'
    have h_swap_maps_S' : ∀ q ∈ S', Prod.swap q ∈ S' := by
      intro q hq
      have hqS : q ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hq)
      have h_swap_q_mem : Prod.swap q ∈ S := h_swap_maps q hqS
      have hq_ne_swap_p : q ≠ Prod.swap p := (Finset.mem_erase.mp hq).1
      have hq_ne_p : q ≠ p :=
        (Finset.mem_erase.mp (Finset.mem_of_mem_erase hq)).1
      -- Goal: swap q ∈ (S.erase p).erase (swap p) = S'
      apply Finset.mem_erase.mpr
      constructor
      · -- swap q ≠ swap p (otherwise q = p)
        intro h_eq
        apply hq_ne_p
        calc
          q = Prod.swap (Prod.swap q) := rfl
          _ = Prod.swap (Prod.swap p) := by rw [h_eq]
          _ = p := rfl
      · -- swap q ∈ S.erase p
        apply Finset.mem_erase.mpr
        constructor
        · -- swap q ≠ p (otherwise q = swap p)
          intro h_eq
          apply hq_ne_swap_p
          calc
            q = Prod.swap (Prod.swap q) := rfl
            _ = Prod.swap p := by rw [h_eq]
        · exact h_swap_q_mem
    have h_swap_no_fixed_S' : ∀ q ∈ S', Prod.swap q ≠ q := by
      intro q hq
      exact h_swap_no_fixed q (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hq))
    have hS'_even : Even S'.card := ih S' hS'_ssubset h_swap_maps_S' h_swap_no_fixed_S'
    -- Card relation: S.card = S'.card + 2 (removed two distinct elements)
    have h_card_S : S.card = S'.card + 2 := by
      have h1 := Finset.card_erase_of_mem hp
      -- h1: (S.erase p).card = S.card - 1
      have h2 := Finset.card_erase_of_mem hp_swap_mem_erase
      -- h2: S'.card = (S.erase p).card - 1
      -- From hp and hp_swap_mem_erase, both cardinals are ≥ 1, so subtraction is genuine
      have hS_card_ge_1 : 1 ≤ S.card := Finset.one_le_card.mpr ⟨p, hp⟩
      have h_erase_card_ge_1 : 1 ≤ (S.erase p).card :=
        Finset.one_le_card.mpr ⟨Prod.swap p, hp_swap_mem_erase⟩
      have h1_add : (S.erase p).card + 1 = S.card := by
        rw [h1]
        rw [Nat.sub_add_cancel hS_card_ge_1]
      have h2_add : S'.card + 1 = (S.erase p).card := by
        rw [h2]
        rw [Nat.sub_add_cancel h_erase_card_ge_1]
      calc
        S.card = (S.erase p).card + 1 := by rw [h1_add]
        _ = (S'.card + 1) + 1 := by rw [h2_add]
        _ = S'.card + 2 := by omega
    rcases hS'_even with ⟨k, hk⟩
    exact ⟨k + 1, by omega⟩
  rw [unitDistPairs, Nat.two_mul_div_two_of_even h_even]

/-!
### Lemma 2.4: Coset averaging

By averaging over the torus ℂ^f/Λ with Haar measure, there exists a coset
a+Λ and a subset X of its intersection with the polydisc B_R such that
the number E of ordered U-pairs in X satisfies E ≥ e^{γf/2} · |X|.

We package the result in a dedicated structure.
-/

/-- Result of the coset averaging lemma: a coset a+Λ, its intersection X
    with the polydisc, and the crucial counting estimate. -/
structure GoodCoset (A : AdmissibleFamily) (R : ℝ) where
  a : Fin A.f → ℂ
  X : Set (Fin A.f → ℂ)
  hX_sub  : X ⊆ shift a A.Λ.carrier ∩ polydisc A.f R
  hX_fin  : Set.Finite X
  hX_ne   : X.Nonempty
  h_count : let N := hX_fin.toFinset.card
            let E := ((hX_fin.toFinset ×ˢ hX_fin.toFinset).filter
                        (λ (p : (Fin A.f → ℂ) × (Fin A.f → ℂ)) => p.2 - p.1 ∈ A.U)).card
            (E : ℝ) ≥ Real.exp (A.γ / 2 * (A.f : ℝ)) * (N : ℝ)

/-- The existence of a good coset is Axiom 3, relying on Haar measure
    on the torus ℂ^f/Λ.  Declared as `def` (not `lemma`) because
    it returns a `GoodCoset` structure, not a `Prop`. -/
def exists_good_coset (A : AdmissibleFamily) (R : ℝ) (hR : R > 1/2)
    (hρ : Real.log (rho R) > -(A.γ / 2)) : GoodCoset A R := by
  -- The full proof requires Haar measure on the torus.
  sorry

/-!
### Lemma 2.6: Size bound

The number of points in the coset slice is at most exponential in f.
This is a sup-norm packing argument (Axiom 4).
-/

lemma size_bound (A : AdmissibleFamily) (R : ℝ) (a : Fin A.f → ℂ)
    (X : Set (Fin A.f → ℂ))
    (hX : X ⊆ shift a A.Λ.carrier ∩ polydisc A.f R)
    (hXfin : Set.Finite X)
    (h_4RD_gt_one : 4 * R * A.D > 1) :
    let n := hXfin.toFinset.card
    (n : ℝ) ≤ Real.exp ((2 * Real.log (4 * R * A.D)) * (A.f : ℝ)) := by
  sorry

/-!
### Theorem 2.3: From admissible family to planar point set
-/

/-- **Theorem 2.3 (parametric form).**  Given R > 1/2 satisfying the ρ-condition,
    and an admissible family A, produce a planar set P with:
    - |P| ≥ 1
    - |P| ≥ exp(γ/2 · f)  (size lower bound, from E ≤ N² and E ≥ exp·N)
    - |P| ≤ exp(2·log(4RD) · f)  (size upper bound, from sup-norm packing)
    - ν(P) ≥ ½ · exp(γ/2 · f) · |P|  (unit-distance lower bound)

    This is the version used in the proof of Theorem 1.1, where R is fixed
    globally so that δ = γ/(4B) is the same for all families in the tower. -/
theorem planar_set_from_datum (A : AdmissibleFamily) (R : ℝ) (hR : R > 1/2)
    (hρ : Real.log (rho R) > -(A.γ / 2))
    (h_4RD_gt_one : 4 * R * A.D > 1) :
    ∃ (P : Finset (ℝ × ℝ)), P.card ≥ 1 ∧
      (P.card : ℝ) ≥ Real.exp (A.γ / 2 * (A.f : ℝ)) ∧
      (P.card : ℝ) ≤ Real.exp (2 * Real.log (4 * R * A.D) * (A.f : ℝ)) ∧
      (unitDistPairs P : ℝ) ≥ (1/2 : ℝ) * Real.exp (A.γ / 2 * (A.f : ℝ)) * (P.card : ℝ) := by
  -- Step 1: obtain a good coset via averaging (Axiom 3)
  obtain ⟨a, X, hX_sub, hX_fin, hX_ne, h_count⟩ := exists_good_coset A R hR hρ
  -- Step 2: set up the projection and finsets
  let π₁ : (Fin A.f → ℂ) → ℂ := fun z => z (fin0 A.hf)
  have h_coset_sub : X ⊆ shift a A.Λ.carrier := fun x hx => (hX_sub hx).left
  have h_proj_inj : ∀ x ∈ X, ∀ y ∈ X, π₁ x = π₁ y → x = y :=
    projection_injective A X h_coset_sub
  let X_finset : Finset (Fin A.f → ℂ) := hX_fin.toFinset
  have hX_finset_mem : ∀ x, x ∈ X_finset ↔ x ∈ X := fun x => Set.Finite.mem_toFinset hX_fin
  let re_im : ℂ → ℝ × ℝ := fun z => (z.re, z.im)
  have h_re_im_inj : Function.Injective re_im := by
    intro a b h; apply Complex.ext
    · exact congr_arg Prod.fst h
    · exact congr_arg Prod.snd h
  -- Step 3: build the planar point set P
  let P : Finset (ℝ × ℝ) := (X_finset.image π₁).image re_im
  have h_proj_inj_on : ∀ x ∈ X_finset, ∀ y ∈ X_finset, π₁ x = π₁ y → x = y := by
    intro x hx y hy h
    exact h_proj_inj x ((hX_finset_mem x).mp hx) y ((hX_finset_mem y).mp hy) h
  have h_card_image_π₁ : (X_finset.image π₁).card = X_finset.card :=
    Finset.card_image_of_injOn (fun x hx y hy h => h_proj_inj_on x hx y hy h)
  have h_card_eq_nat : P.card = X_finset.card := by
    rw [show P.card = (X_finset.image π₁).card from Finset.card_image_of_injective _ h_re_im_inj,
        h_card_image_π₁]
  have h_card_eq : (P.card : ℝ) = (X_finset.card : ℝ) := by exact_mod_cast h_card_eq_nat
  have hP_nonempty : P.Nonempty := by
    rcases hX_ne with ⟨x, hx⟩
    exact ⟨re_im (π₁ x), Finset.mem_image.mpr ⟨π₁ x,
      Finset.mem_image.mpr ⟨x, (hX_finset_mem x).mpr hx, rfl⟩, rfl⟩⟩
  have hP_card_ge_one : P.card ≥ 1 := Finset.one_le_card.mpr hP_nonempty
  -- Step 4: prove |P| ≥ exp(γ/2 · f) using E ≤ N² and E ≥ exp · N
  let N_val := X_finset.card
  let E_finset := (X_finset ×ˢ X_finset).filter
      (fun (p : (Fin A.f → ℂ) × (Fin A.f → ℂ)) => p.2 - p.1 ∈ A.U)
  have hN_pos : (N_val : ℝ) > 0 :=
    by exact_mod_cast Finset.card_pos.mpr (hX_fin.toFinset_nonempty.mpr hX_ne)
  have h_E_le_Nsq : (E_finset.card : ℝ) ≤ (N_val : ℝ) ^ 2 := by
    have h_sub : E_finset ⊆ X_finset ×ˢ X_finset := Finset.filter_subset _ _
    calc (E_finset.card : ℝ)
        ≤ ((X_finset ×ˢ X_finset).card : ℝ) := by exact_mod_cast Finset.card_le_card h_sub
      _ = (N_val : ℝ) ^ 2 := by push_cast [Finset.card_product]; ring
  have h_P_lower : (P.card : ℝ) ≥ Real.exp (A.γ / 2 * (A.f : ℝ)) := by
    rw [h_card_eq]
    -- exp · N ≤ E ≤ N², so exp ≤ N (canceling N > 0)
    have h_mul : Real.exp (A.γ / 2 * (A.f : ℝ)) * N_val ≤ N_val * N_val :=
      calc Real.exp (A.γ / 2 * (A.f : ℝ)) * N_val
          ≤ E_finset.card := h_count
        _ ≤ N_val ^ 2 := h_E_le_Nsq
        _ = N_val * N_val := by ring
    exact le_of_mul_le_mul_right h_mul hN_pos
  -- Step 5: lower bound on ν(P) via the injection E_finset → ordered unit-distance pairs
  have h_edges_lower : (unitDistPairs P : ℝ) ≥
      (1/2 : ℝ) * Real.exp (A.γ / 2 * (A.f : ℝ)) * (P.card : ℝ) := by
    let E_ord := (P.offDiag).filter (fun ⟨x, y⟩ => distSq x y = 1)
    have h_ord_eq : (E_ord.card : ℝ) = 2 * (unitDistPairs P : ℝ) := by
      exact_mod_cast card_ordered_unit_pairs_eq_two_mul_unitDistPairs P
    have h_card_le : (E_finset.card : ℝ) ≤ (E_ord.card : ℝ) := by
      let φ : (Fin A.f → ℂ) × (Fin A.f → ℂ) → (ℝ × ℝ) × (ℝ × ℝ) :=
        fun p => (re_im (π₁ p.1), re_im (π₁ p.2))
      apply Nat.cast_le.mpr
      apply Finset.card_le_card_of_injOn φ
      · intro ⟨x, y⟩ hp
        obtain ⟨h_prod, hu⟩ := Finset.mem_filter.mp hp
        obtain ⟨hx, hy⟩ := Finset.mem_product.mp h_prod
        have hu_mod : ‖(y - x) (fin0 A.hf)‖ = 1 := A.hU_mod _ hu (fin0 A.hf)
        have hx_P : re_im (π₁ x) ∈ P :=
          Finset.mem_image.mpr ⟨π₁ x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, rfl⟩
        have hy_P : re_im (π₁ y) ∈ P :=
          Finset.mem_image.mpr ⟨π₁ y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, rfl⟩
        -- distSq(re_im(π₁ x), re_im(π₁ y)) = 1
        have h_dist : distSq (re_im (π₁ x)) (re_im (π₁ y)) = 1 := by
          simp only [distSq, re_im, π₁]
          -- Show ‖(y-x)(fin0)‖^2 = re^2 + im^2 via abs_apply + sq_sqrt
          have h_norm_sq : ‖(y - x) (fin0 A.hf)‖ ^ 2 =
              ((y - x) (fin0 A.hf)).re ^ 2 + ((y - x) (fin0 A.hf)).im ^ 2 := by
            have h : ‖(y - x) (fin0 A.hf)‖ ^ 2 = normSq ((y - x) (fin0 A.hf)) := by
              simp [Complex.norm_def, Real.sq_sqrt (normSq_nonneg _)]
            rw [h, normSq_apply]; ring
          have hre : ((y - x) (fin0 A.hf)).re = (y (fin0 A.hf)).re - (x (fin0 A.hf)).re := by
            simp [Pi.sub_apply, sub_re]
          have him : ((y - x) (fin0 A.hf)).im = (y (fin0 A.hf)).im - (x (fin0 A.hf)).im := by
            simp [Pi.sub_apply, sub_im]
          have hns2 : ((y (fin0 A.hf)).re - (x (fin0 A.hf)).re) ^ 2 +
                      ((y (fin0 A.hf)).im - (x (fin0 A.hf)).im) ^ 2 = 1 := by
            rw [← hre, ← him, ← h_norm_sq, hu_mod]; norm_num
          linarith
        -- re_im(π₁ x) ≠ re_im(π₁ y)
        have hne : re_im (π₁ x) ≠ re_im (π₁ y) := by
          intro heq
          have hπ : x (fin0 A.hf) = y (fin0 A.hf) := h_re_im_inj heq
          have h1 : (y - x) (fin0 A.hf) = y (fin0 A.hf) - x (fin0 A.hf) := Pi.sub_apply y x _
          rw [h1, ← hπ, sub_self, norm_zero] at hu_mod
          exact absurd hu_mod (by norm_num)
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_offDiag.mpr ⟨hx_P, hy_P, hne⟩, h_dist⟩
      · intro ⟨x1, y1⟩ hp1 ⟨x2, y2⟩ hp2 heq
        simp only [φ, Prod.mk.injEq] at heq
        obtain ⟨h1, h2⟩ := heq
        have ⟨hprod1, _⟩ := Finset.mem_filter.mp hp1
        have ⟨hprod2, _⟩ := Finset.mem_filter.mp hp2
        have ⟨hx1, hy1⟩ := Finset.mem_product.mp hprod1
        have ⟨hx2, hy2⟩ := Finset.mem_product.mp hprod2
        congr 1
        · exact h_proj_inj x1 ((hX_finset_mem x1).mp hx1) x2 ((hX_finset_mem x2).mp hx2)
              (h_re_im_inj h1)
        · exact h_proj_inj y1 ((hX_finset_mem y1).mp hy1) y2 ((hX_finset_mem y2).mp hy2)
              (h_re_im_inj h2)
    calc (unitDistPairs P : ℝ) = (E_ord.card : ℝ) / 2 := by linarith
      _ ≥ (E_finset.card : ℝ) / 2 := by gcongr
      _ ≥ (Real.exp (A.γ / 2 * (A.f : ℝ)) * (X_finset.card : ℝ)) / 2 := by gcongr
      _ = (Real.exp (A.γ / 2 * (A.f : ℝ)) * (P.card : ℝ)) / 2 := by rw [h_card_eq]
      _ = (1/2 : ℝ) * Real.exp (A.γ / 2 * (A.f : ℝ)) * (P.card : ℝ) := by ring
  -- Step 6: size upper bound |P| ≤ exp(2·log(4RD)·f) via sup-norm packing
  have h_P_upper : (P.card : ℝ) ≤ Real.exp (2 * Real.log (4 * R * A.D) * (A.f : ℝ)) := by
    rw [h_card_eq]
    dsimp [X_finset]
    have := size_bound A R a X hX_sub hX_fin h_4RD_gt_one
    simp only at this
    linarith
  exact ⟨P, hP_card_ge_one, h_P_lower, h_P_upper, h_edges_lower⟩

/-- **Theorem 2.3.** Given an admissible family A, there exists a planar point set
    P ⊂ ℝ² and δ > 0 such that ν(P) ≥ ½·|P|^{1+2δ}.

    Here δ = γ/(8·log(4RD)) depends on γ, D, and R (all independent of f).

    The proof chains three lemmas:
    1. Lemma 2.4 (exists_good_coset): choose a coset with many U-pairs
    2. Lemma 2.5 (projection_injective): map to ℂ via first coordinate
    3. Lemma 2.6 (size_bound): control |P| relative to f

    Then algebra converts f-dependence to |P|-dependence:
    ν(P) ≥ ½·e^{γf/2}·|P| ≥ ½·|P|^{γ/(2B)}·|P| = ½·|P|^{1+2δ}. -/
theorem admissible_family_to_planar_set (A : AdmissibleFamily) :
    ∃ (P : Finset (ℝ × ℝ)) (δ : ℝ), δ > 0 ∧ P.card ≥ 1 ∧
      (unitDistPairs P : ℝ) ≥ (1/2 : ℝ) * ((P.card : ℝ) ^ (1 + 2*δ)) := by
  -- Step 1: choose R > 1/2 such that log ρ(R) > -γ/2 and 4RD > 1
  have hγ2_pos : A.γ / 2 > 0 := half_pos A.hγ
  obtain ⟨R, hR, hρ, h_4RD_gt_one⟩ := exists_R_log_rho_gt (A.γ / 2) hγ2_pos A.D A.hD
  have hR_pos : R > 0 := by linarith
  -- Step 2: define B = 2·log(4RD) and δ = γ/(4B)
  set B := 2 * Real.log (4 * R * A.D) with hB_def
  have hB_pos : B > 0 := by
    have hlog : Real.log (4 * R * A.D) > 0 := Real.log_pos h_4RD_gt_one
    positivity
  set δ := A.γ / (4 * B) with hδ_def
  have hδ_pos : δ > 0 := div_pos A.hγ (by positivity)
  -- Algebraic identity: γ/2 = 2δB, used to convert exponents
  have h_γ_over_2_eq_2δB : A.γ / 2 = 2 * δ * B := by
    rw [hδ_def]
    field_simp [show B ≠ 0 from by linarith [hB_pos]]
    ring
  -- Step 3: obtain a good coset via averaging (Axiom 3)
  obtain ⟨a, X, hX_sub, hX_fin, hX_ne, h_count⟩ := exists_good_coset A R hR hρ
  -- Step 4: project to first complex coordinate, then to ℝ×ℝ
  let π₁ : (Fin A.f → ℂ) → ℂ := λ z => z (fin0 A.hf)
  have h_coset_sub : X ⊆ shift a A.Λ.carrier := by
    intro x hx; exact (hX_sub hx).left
  have h_proj_inj : ∀ x ∈ X, ∀ y ∈ X, π₁ x = π₁ y → x = y :=
    projection_injective A X h_coset_sub
  -- Work with Finsets for counting
  let X_finset : Finset (Fin A.f → ℂ) := hX_fin.toFinset
  have hX_finset_mem : ∀ x, x ∈ X_finset ↔ x ∈ X := λ x =>
    Set.Finite.mem_toFinset hX_fin
  -- Projection ℂ → ℝ×ℝ is a bijection that preserves Euclidean distance
  let re_im : ℂ → ℝ × ℝ := λ z => (z.re, z.im)
  have h_re_im_inj : Function.Injective re_im := by
    intro a b h
    apply Complex.ext
    · exact congr_arg Prod.fst h
    · exact congr_arg Prod.snd h
  -- Build the planar point set P
  let P : Finset (ℝ × ℝ) := (X_finset.image π₁).image re_im
  -- Step 5: cardinality |P| = |X| (projections are injective on X_finset)
  have h_proj_inj_on : ∀ x ∈ X_finset, ∀ y ∈ X_finset, π₁ x = π₁ y → x = y := by
    intro x hx y hy h
    exact h_proj_inj x ((hX_finset_mem x).mp hx) y ((hX_finset_mem y).mp hy) h
  have h_card_image_π₁ : (X_finset.image π₁).card = X_finset.card :=
    Finset.card_image_of_injOn (by
      intro x hx y hy h; exact h_proj_inj_on x hx y hy h)
  have h_card_image_re_im : P.card = (X_finset.image π₁).card :=
    Finset.card_image_of_injective _ h_re_im_inj
  have h_card_eq_nat : P.card = X_finset.card := by
    rw [h_card_image_re_im, h_card_image_π₁]
  have h_card_eq : (P.card : ℝ) = (X_finset.card : ℝ) := by exact_mod_cast h_card_eq_nat
  -- P is nonempty because X is nonempty
  have hP_nonempty : P.Nonempty := by
    rcases hX_ne with ⟨x, hx⟩
    have hx_fin : x ∈ X_finset := (hX_finset_mem x).mpr hx
    have h_π₁_mem : π₁ x ∈ X_finset.image π₁ :=
      Finset.mem_image.mpr ⟨x, hx_fin, rfl⟩
    have hP_mem : re_im (π₁ x) ∈ P :=
      Finset.mem_image.mpr ⟨π₁ x, h_π₁_mem, rfl⟩
    exact ⟨re_im (π₁ x), hP_mem⟩
  have hP_card_ge_one : P.card ≥ 1 := Finset.one_le_card.mpr hP_nonempty
  -- Step 6: bound on unit-distance pairs
  -- The key combinatorial step: each ordered U-pair (x,y) in X projects via
  -- φ(x,y) = (re_im(π₁ x), re_im(π₁ y)) to an ordered unit-distance pair in P.
  -- The projection is injective (π₁ injective on X, re_im injective on ℂ),
  -- so the U-pair count E is ≤ the ordered unit-distance pair count in P.
  -- Since ordered unit-distance pairs = 2·unitDistPairs P (by the counting lemma),
  -- we get ν(P) ≥ E/2 ≥ ½·e^{γf/2}·|P|.
  have h_edges_lower : (unitDistPairs P : ℝ) ≥
      (1/2 : ℝ) * Real.exp (A.γ / 2 * (A.f : ℝ)) * (P.card : ℝ) := by
    let E_finset := (X_finset ×ˢ X_finset).filter
      (λ (p : (Fin A.f → ℂ) × (Fin A.f → ℂ)) => p.2 - p.1 ∈ A.U)
    let E_ord := (P.offDiag).filter (λ ⟨x, y⟩ => distSq x y = 1)
    -- From the counting lemma: ordered pairs count = 2 * unitDistPairs
    have h_ord_eq : (E_ord.card : ℝ) = 2 * (unitDistPairs P : ℝ) := by
      have h_nat := card_ordered_unit_pairs_eq_two_mul_unitDistPairs P
      exact_mod_cast h_nat
    -- The projection map φ is injective on E_finset and maps into E_ord (see comment)
    have h_card_le : (E_finset.card : ℝ) ≤ (E_ord.card : ℝ) := by
      let φ : (Fin A.f → ℂ) × (Fin A.f → ℂ) → (ℝ × ℝ) × (ℝ × ℝ) :=
        fun p => (re_im (π₁ p.1), re_im (π₁ p.2))
      apply Nat.cast_le.mpr
      apply Finset.card_le_card_of_injOn φ
      · intro ⟨x, y⟩ hp
        obtain ⟨h_prod, hu⟩ := Finset.mem_filter.mp hp
        obtain ⟨hx, hy⟩ := Finset.mem_product.mp h_prod
        have hu_mod : ‖(y - x) (fin0 A.hf)‖ = 1 := A.hU_mod _ hu (fin0 A.hf)
        have hx_P : re_im (π₁ x) ∈ P :=
          Finset.mem_image.mpr ⟨π₁ x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, rfl⟩
        have hy_P : re_im (π₁ y) ∈ P :=
          Finset.mem_image.mpr ⟨π₁ y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, rfl⟩
        have h_dist : distSq (re_im (π₁ x)) (re_im (π₁ y)) = 1 := by
          simp only [distSq, re_im, π₁]
          have h_norm_sq : ‖(y - x) (fin0 A.hf)‖ ^ 2 =
              ((y - x) (fin0 A.hf)).re ^ 2 + ((y - x) (fin0 A.hf)).im ^ 2 := by
            have h : ‖(y - x) (fin0 A.hf)‖ ^ 2 = normSq ((y - x) (fin0 A.hf)) := by
              simp [Complex.norm_def, Real.sq_sqrt (normSq_nonneg _)]
            rw [h, normSq_apply]; ring
          have hre : ((y - x) (fin0 A.hf)).re = (y (fin0 A.hf)).re - (x (fin0 A.hf)).re := by
            simp [Pi.sub_apply, sub_re]
          have him : ((y - x) (fin0 A.hf)).im = (y (fin0 A.hf)).im - (x (fin0 A.hf)).im := by
            simp [Pi.sub_apply, sub_im]
          have hns2 : ((y (fin0 A.hf)).re - (x (fin0 A.hf)).re) ^ 2 +
                      ((y (fin0 A.hf)).im - (x (fin0 A.hf)).im) ^ 2 = 1 := by
            rw [← hre, ← him, ← h_norm_sq, hu_mod]; norm_num
          linarith
        have hne : re_im (π₁ x) ≠ re_im (π₁ y) := by
          intro heq
          have hπ : x (fin0 A.hf) = y (fin0 A.hf) := h_re_im_inj heq
          have h1 : (y - x) (fin0 A.hf) = y (fin0 A.hf) - x (fin0 A.hf) := Pi.sub_apply y x _
          rw [h1, ← hπ, sub_self, norm_zero] at hu_mod
          exact absurd hu_mod (by norm_num)
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_offDiag.mpr ⟨hx_P, hy_P, hne⟩, h_dist⟩
      · intro ⟨x1, y1⟩ hp1 ⟨x2, y2⟩ hp2 heq
        simp only [φ, Prod.mk.injEq] at heq
        obtain ⟨h1, h2⟩ := heq
        have ⟨hprod1, _⟩ := Finset.mem_filter.mp hp1
        have ⟨hprod2, _⟩ := Finset.mem_filter.mp hp2
        have ⟨hx1, hy1⟩ := Finset.mem_product.mp hprod1
        have ⟨hx2, hy2⟩ := Finset.mem_product.mp hprod2
        congr 1
        · exact h_proj_inj x1 ((hX_finset_mem x1).mp hx1) x2 ((hX_finset_mem x2).mp hx2)
              (h_re_im_inj h1)
        · exact h_proj_inj y1 ((hX_finset_mem y1).mp hy1) y2 ((hX_finset_mem y2).mp hy2)
              (h_re_im_inj h2)
    -- From h_count: E ≥ e^{γf/2} · N, and h_card_eq: N = |P|
    calc
      (unitDistPairs P : ℝ) = (E_ord.card : ℝ) / 2 := by linarith
      _ ≥ (E_finset.card : ℝ) / 2 := by gcongr
      _ ≥ (Real.exp (A.γ / 2 * (A.f : ℝ)) * (X_finset.card : ℝ)) / 2 := by
        gcongr
      _ = (Real.exp (A.γ / 2 * (A.f : ℝ)) * (P.card : ℝ)) / 2 := by rw [h_card_eq]
      _ = (1/2 : ℝ) * Real.exp (A.γ / 2 * (A.f : ℝ)) * (P.card : ℝ) := by ring
  -- Step 7: convert f-dependence to |P|-dependence via the size bound.
  -- From |P| ≤ e^{Bf} we deduce e^{γf/2} ≥ |P|^{γ/(2B)} = |P|^{2δ}.
  -- Then ν(P) ≥ ½·e^{γf/2}·|P| ≥ ½·|P|^{2δ}·|P| = ½·|P|^{1+2δ}.
  have h_final : (unitDistPairs P : ℝ) ≥ (1/2 : ℝ) * ((P.card : ℝ) ^ (1 + 2*δ)) := by
    have h_size : (P.card : ℝ) ≤ Real.exp (B * (A.f : ℝ)) := by
      rw [hB_def, h_card_eq]
      dsimp [X_finset]
      exact size_bound A R a X hX_sub hX_fin h_4RD_gt_one
    have hPcard_pos : (0 : ℝ) < (P.card : ℝ) :=
      by exact_mod_cast Nat.pos_of_ne_zero (Finset.card_ne_zero.mpr hP_nonempty)
    have h_exp_bound : Real.exp (A.γ / 2 * (A.f : ℝ)) ≥ (P.card : ℝ) ^ (2*δ) := by
      rw [Real.rpow_def_of_pos hPcard_pos]
      apply Real.exp_le_exp.mpr
      have hlog_le : Real.log (P.card : ℝ) ≤ B * (A.f : ℝ) := by
        have h := Real.log_le_log hPcard_pos h_size
        rwa [Real.log_exp] at h
      calc Real.log (P.card : ℝ) * (2 * δ)
          ≤ B * (A.f : ℝ) * (2 * δ) :=
            mul_le_mul_of_nonneg_right hlog_le (by positivity)
        _ = A.γ / 2 * (A.f : ℝ) := by rw [h_γ_over_2_eq_2δB]; ring
    calc
      (unitDistPairs P : ℝ) ≥ (1/2 : ℝ) * Real.exp (A.γ / 2 * (A.f : ℝ)) * (P.card : ℝ) :=
        h_edges_lower
      _ ≥ (1/2 : ℝ) * ((P.card : ℝ) ^ (2*δ)) * (P.card : ℝ) := by
        gcongr
      _ = (1/2 : ℝ) * ((P.card : ℝ) ^ (1 + 2*δ)) := by
        have hPcard_pos : (0 : ℝ) < (P.card : ℝ) :=
          by exact_mod_cast Nat.pos_of_ne_zero (Finset.card_ne_zero.mpr hP_nonempty)
        rw [show (1 : ℝ) + 2 * δ = 2 * δ + 1 from by ring,
            Real.rpow_add hPcard_pos, Real.rpow_one]
        ring
  exact ⟨P, δ, hδ_pos, hP_card_ge_one, h_final⟩
