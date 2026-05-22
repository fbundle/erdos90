import Mathlib
import Erdos90.Defs

/-!
# Arithmetic postulates (Section 3 of the paper)

The existence of an infinite tower of totally real fields with prescribed
splitting and bounded root discriminant, constructed via Golod-Shafarevich
theory and Chebotarev density.

We package the conclusion as an explicit `AdmissibleFamily` structure
and a theorem proving its existence (from number-theoretic defs with sorry).
-/

/-- First element of `Fin f` when `f ≥ 1`. -/
def fin0 {f : ℕ} (hf : f ≥ 1) : Fin f := ⟨0, by omega⟩

/-- A level of the admissible tower: degree f, denominator D,
    Minkowski lattice Λ ⊂ ℂ^f, and a set U ⊂ Λ of norm-one elements.

    In the paper: L is totally real of degree f, K = L(i) is CM,
    Λ = Φ(D⁻¹O_K) under the Minkowski embedding Φ,
    U = {Φ(u) : u ∈ K^×, u·c(u) = 1} obtained from split primes
    via the class-group pigeonhole (Proposition 2.2). -/
structure AdmissibleFamily where
  f    : ℕ
  hf   : f ≥ 1
  D    : ℝ
  hD   : D > 0
  γ    : ℝ
  hγ   : γ > 0
  Λ    : AddSubgroup (Fin f → ℂ)
  U    : Finset (Fin f → ℂ)
  -- All coordinates of every u ∈ U have modulus 1
  hU_mod   : ∀ u ∈ U, ∀ r : Fin f, ‖u r‖ = 1
  -- U ⊂ Λ (norm-1 elements lie in the lattice)
  hU_in_Λ  : ∀ u ∈ U, (u : Fin f → ℂ) ∈ Λ
  -- |U| ≥ e^{γ f}
  hU_size  : (U.card : ℝ) ≥ Real.exp (γ * (f : ℝ))
  -- Separation: nonzero lattice elements have first coordinate ≥ D⁻¹ in modulus
  hΛ_sep   : ∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf)‖ ≥ D⁻¹
  -- Coset averaging (Lemma 2.4): for any R > 1/2 with log ρ(R) > -γ/2, there exists
  -- a coset a+Λ whose intersection X with the polydisc B_R satisfies E ≥ exp(γf/2)·|X|,
  -- where E counts ordered pairs (x,y) ∈ X² with y-x ∈ U.
  h_coset_avg : ∀ (R : ℝ), R > 1/2 → Real.log (rho R) > -(γ / 2) →
      CosetAvgWitness f Λ U R γ

/-! `exists_admissible_family` is a **theorem** proved in `Erdos90/NumberField.lean`
    from number-theoretic defs with sorry (Props 2.2, 3.2–3.8) + analytic lemmas. -/
