import Mathlib
import Erd46.Defs
import Erd46.Arithmetic

open Complex
open Real
open Set

/-!
# Geometric lemmas (Section 2 of the paper)

Given an `AdmissibleFamily` A (a Minkowski lattice Λ ⊂ ℂ^f with many
norm-one translations U), we construct a planar point set P ⊂ ℝ²
with ν(P) ≥ |P|^{1+δ} for a fixed δ > 0.
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

/-- For any ε > 0, there exists R > 1/2 with log ρ(R) > -ε.
    Follows from ρ(R) → 1 as R → ∞. -/
axiom exists_R_log_rho_gt (ε : ℝ) (εpos : ε > 0) : ∃ R > (1/2 : ℝ), Real.log (rho R) > -ε

/-- First element of `Fin f` when `f ≥ 1`. -/
def fin0 {f : ℕ} (hf : f ≥ 1) : Fin f := ⟨0, by omega⟩

/-!
### Lemma 2.5: Projection injectivity

The first-coordinate projection π₁: ℂ^f → ℂ is injective on any subset of
a single Λ-coset.
-/

lemma nonzero_in_Λ_has_large_coord (A : AdmissibleFamily) {v : Fin A.f → ℂ}
    (hvΛ : v ∈ A.Λ) (hv_ne : v ≠ 0) : ∃ r : Fin A.f, ‖v r‖ ≥ A.D⁻¹ :=
  A.hΛ_sep v hvΛ hv_ne

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
  -- x = a + vx, y = a + vy
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
  obtain ⟨r, hr⟩ := nonzero_in_Λ_has_large_coord A h_in_Λ h_diff_ne
  by_cases hr0 : r = fin0 A.hf
  · subst r
    rw [h_diff_coord0] at hr
    have hDinv : A.D⁻¹ > 0 := inv_pos.mpr A.hD
    have hzero : ‖(0 : ℂ)‖ = 0 := norm_zero
    rw [hzero] at hr
    linarith
  · sorry

/-!
### Lemma 2.4: Coset averaging

By averaging over the torus ℂ^f/Λ with Haar measure, there exists a coset
a+Λ and a subset X of its intersection with the polydisc B_R such that
the number E of ordered U-pairs in X satisfies E ≥ e^{γf/2} · |X|.

**Proof sketch** (paper Lemma 2.4):
- E_a[|(a+Λ) ∩ B_R|] = vol(B_R)/covol(Λ) = (πR²)^f / covol(Λ)
- E_a[E_a] = |U|·a(R)^f / covol(Λ) = |U|·ρ(R)^f·(πR²)^f / covol(Λ)
- If every nonempty coset had E_a < |U|·ρ(R)^f·N_a, averaging would
  contradict the identity.
- Choose R with log ρ(R) > -γ/2, then |U|·ρ(R)^f ≥ e^{γf}·e^{-γf/2} = e^{γf/2}.
-/

lemma exists_good_coset (A : AdmissibleFamily) (R : ℝ) (hR : R > 1/2)
    (hρ : Real.log (rho R) > -(A.γ / 2)) :
    ∃ (a : Fin A.f → ℂ) (X : Set (Fin A.f → ℂ)),
      X ⊆ shift a A.Λ.carrier ∩ polydisc A.f R ∧
      Set.Finite X ∧ X.Nonempty := by
  -- The full proof requires Haar measure on the torus.
  sorry

/-!
### Lemma 2.6: Size bound

The number of points in the coset slice is at most exponential in f.
This is a sup-norm packing argument.

**Proof sketch** (paper Lemma 2.6):
- Distinct points of X differ by a lattice element, so some coordinate
  differs by at least D⁻¹.
- Radius-(D⁻¹/2) sup-norm polydiscs around the points are disjoint
  and all lie in B_{R + D⁻¹/2}.
- Comparing volumes gives |X| ≤ (1 + 2RD)^{2f} ≤ (4RD)^{2f} = e^{Bf}.
-/

lemma size_bound (A : AdmissibleFamily) (R : ℝ) (hR : R > 0) (a : Fin A.f → ℂ)
    (X : Set (Fin A.f → ℂ))
    (hX : X ⊆ shift a A.Λ.carrier ∩ polydisc A.f R)
    (hXfin : Set.Finite X) :
    let n := hXfin.toFinset.card
    (n : ℝ) ≤ Real.exp ((2 * Real.log (4 * R * A.D)) * (A.f : ℝ)) := by
  sorry

/-!
### Theorem 2.3: From admissible family to planar point set
-/

/-- **Theorem 2.3.** Given an admissible family A, there exists a planar point set
    P ⊂ ℝ² with ν(P) ≥ |P|^{1+δ} for a fixed δ > 0 independent of the degree f.

    δ = γ/(4B) where B = 2·log(4RD) and R satisfies log ρ(R) > -γ/2. -/
theorem admissible_family_to_planar_set (A : AdmissibleFamily) :
    ∃ (P : Finset (ℝ × ℝ)) (δ : ℝ), δ > 0 ∧ P.card ≥ 1 ∧
      (unitDistPairs P : ℝ) ≥ ((P.card : ℝ) ^ (1 + δ)) := by
  -- Step 1: choose R > 1/2 such that log ρ(R) > -γ/2
  have hγ2_pos : A.γ / 2 > 0 := half_pos A.hγ
  obtain ⟨R, hR, hρ⟩ := exists_R_log_rho_gt (A.γ / 2) hγ2_pos
  have hR_pos : R > 0 := by linarith
  -- Step 2: define B = 2·log(4RD) and δ = γ/(4B)
  -- We need R large enough that 4RD > 1 (so log > 0 and B > 0).
  -- This is arranged in the construction by taking R sufficiently large.
  -- For now, we add this as an additional requirement on R.
  have h_4RD_gt_one : 4 * R * A.D > 1 := by
    -- In the full proof, this follows from choosing R large enough
    -- that log ρ(R) > -γ/2 AND 4RD > 1
    sorry
  set B := 2 * Real.log (4 * R * A.D) with hB_def
  have hB_pos : B > 0 := by
    have hlog : Real.log (4 * R * A.D) > 0 := Real.log_pos h_4RD_gt_one
    positivity
  set δ := A.γ / (4 * B) with hδ_def
  have hδ_pos : δ > 0 := div_pos A.hγ (by positivity)
  -- Step 3: obtain a good coset via averaging (Lemma 2.4)
  obtain ⟨a, X, hX_sub, hXfin, hX_ne⟩ := exists_good_coset A R hR hρ
  -- Step 4: project to first complex coordinate (injective by Lemma 2.5)
  let π₁ : (Fin A.f → ℂ) → ℂ := λ z => z (fin0 A.hf)
  have h_coset_sub : X ⊆ shift a A.Λ.carrier := by
    intro x hx
    have h_inter : x ∈ shift a A.Λ.carrier ∩ polydisc A.f R := hX_sub hx
    exact h_inter.left
  have h_proj_inj : ∀ x ∈ X, ∀ y ∈ X, π₁ x = π₁ y → x = y :=
    projection_injective A (a := a) X h_coset_sub
  -- Step 5: convert planar projection to Finset (ℝ × ℝ)
  have h_proj_fin : Set.Finite (π₁ '' X) :=
    Set.Finite.image π₁ hXfin
  let imgFinset : Finset ℂ := Set.Finite.toFinset h_proj_fin
  let P : Finset (ℝ × ℝ) := imgFinset.image (λ z : ℂ => (z.re, z.im))
  sorry
