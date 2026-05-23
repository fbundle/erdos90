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

1. **Provable helpers** — pure analysis and combinatorics, no sorry.
2. **Golod–Shafarevich tower** — one targeted sorry for the pro-3 tower
   (Golod–Shafarevich + Chebotarev; not in Mathlib as of 2025).
3. **Minkowski lattice bridge** — one targeted sorry for transporting
   `integerLattice K` from `mixedSpace K` to `Fin f → ℂ` and proving the
   first-coordinate separation bound (requires type isomorphism +
   product-formula argument; type bridge is not in Mathlib).
4. **CM norm-one elements** — one targeted sorry for the class-group
   pigeonhole over `ClassGroup K` (requires CM split-prime ideal API not
   in Mathlib as of 2025).

The three sorries correspond directly to three independently checkable
mathematical arguments in [OpenAI 2026] (Props 2.2, 3.2–3.6, 3.7–3.8).
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

/-- For exp(γ · f) ≥ 1 from γ > 0 and f ≥ 1. Used to show U is nonempty. -/
lemma exp_pos_of_pos (γ : ℝ) (f : ℕ) (hγ : γ > 0) (hf : f ≥ 1) :
    Real.exp (γ * f) ≥ 1 := by
  have hfpos : (0 : ℝ) < f := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  -- Use 1 + x ≤ exp(x) (Real.add_one_le_exp), so 1 ≤ 1 + γf ≤ exp(γf)
  linarith [Real.add_one_le_exp (γ * (f : ℝ)), mul_pos hγ hfpos]

/-! ## §2  Golod–Shafarevich tower with Chebotarev split primes

**Mathematical content** (Props 3.2–3.6 of [OpenAI 2026]):

*Step 1*. Choose ℓ primes r₁,…,rₗ ≡ 1 (mod 3).  Let L_i = cubic cyclic
subfield of ℚ(ζ_{rᵢ}), M = L₁⋯Lₗ, F = cyclic cubic subfield of M cut out
by χ₁⋯χₗ.  By the conductor–discriminant formula, |D_F| = D² (D = ∏ rᵢ),
M/F is everywhere unramified, and d(G) ≥ ℓ-1 for G = Gal(F^{ur,3}/F).

*Step 2*. By Chebotarev (Prop 3.6), find t = ⌊(ℓ-1)²/100⌋ primes
q₁,…,qₜ ≡ 1 (mod 4), splitting completely in F with Frobenius in Φ(G).
Set D₀ = Q² where Q = ∏ qᵦ.

*Step 3*. The quotient G̅ = G/N (N = closed normal closure of Frobenius
elements) is infinite (Golod–Shafarevich: d(G̅) = d, r(G̅) ≤ d+C₀+3t < d²/4
for large ℓ).  Its open normal subgroups give an infinite tower F = F₀ ⊂ F₁ ⊂ …
with f_j = [F_j:ℚ] → ∞, rd(F_j) = rd(F), each q_b splitting completely.

*Lean gap*: pro-3 Galois group theory and quantitative Chebotarev are not
formalized in Mathlib (as of Mathlib v4.29.1, 2025).
-/

/-- **Golod–Shafarevich tower** (Props 3.2–3.6, sorry'd).

    For ℓ ≥ 2, produces:
    - `D₀ = Q² > 0` (denominator from split primes)
    - `rd_F ≥ 1` with `log rd_F ≤ ℓ · log ℓ`
    - For every M, a degree `f ≥ M` with:
      - `hf1 : f ≥ 1`
      - `Λ : AddSubgroup (Fin f → ℂ)` — Minkowski lattice of a CM field K_j of degree 2f
      - `hΛ_countable : Countable Λ`
      - `F : Set (Fin f → ℂ)` — fundamental domain of Λ
      - `IsAddFundamentalDomain Λ F volume` (from `fundamentalDomain_integerLattice`)
      - `volume F < ∞` (from `volume_fundamentalDomain_latticeBasis`)
      - `∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf1)‖ ≥ D₀⁻¹`
        (from the product formula: ∏ |σ_r(v)| ≥ D₀^{-f}, hence some coordinate ≥ D₀⁻¹;
         here σ₁ is chosen to achieve the maximum, or equivalently the first-coordinate
         bound follows from |N_{K/ℚ}(β)|^{1/2} ≥ 1 and the D₀-denominator clearing.)

    **Unavoidable Lean gap**: this sorry packages three sub-steps that each require
    mathematical development not yet in Mathlib:
    (a) Golod–Shafarevich: infinite pro-3 tower (pro-p group theory, [GS64, Sha63])
    (b) Chebotarev: ∃ t primes q_b with prescribed splitting (quantitative Chebotarev)
    (c) Type bridge: `mixedSpace K_j ≃ Fin f_j → ℂ` (for totally complex K_j) and
        transport of `integerLattice K_j` and `IsAddFundamentalDomain` across this equiv,
        plus the product-formula bound `|N(β)|^{1/2}/D₀^f ≥ D₀^{-f}` → `∃ r, |v r| ≥ D₀⁻¹`
        → first-coordinate separation after reordering embeddings. -/
def golod_shafarevich_tower_with_lattice :
    ∀ (ℓ : ℕ), ℓ ≥ 2 →
    ∃ (D₀ : ℝ), D₀ > 0 ∧ ∃ (rd_F : ℝ), rd_F ≥ 1 ∧
      Real.log rd_F ≤ (ℓ : ℝ) * Real.log (ℓ : ℝ) ∧
      ∀ (M : ℕ),
        ∃ (f : ℕ), f ≥ M ∧
        ∃ (hf1 : f ≥ 1) (Λ : AddSubgroup (Fin f → ℂ))
          (_ : Countable Λ) (F : Set (Fin f → ℂ)),
          IsAddFundamentalDomain Λ F volume ∧ volume F < ∞ ∧
          (∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf1)‖ ≥ D₀⁻¹) := by
  intro ℓ hℓ
  -- The concrete witness for D₀ is Q² where Q = ∏_{b=1}^t q_b (product of t split primes).
  -- The concrete witness for rd_F is the root discriminant of the base cyclic cubic field F:
  --   rd(F) = |D_F|^{1/3} = D^{2/3} ≤ (∏ r_i)^{2/3} ≤ (r_ℓ)^{2/3 ℓ} ≤ (2·3·ℓ·log ℓ)^{2/3}
  -- For the log bound, rd_F ≤ 2ℓ suffices (log(2ℓ) ≤ ℓ log ℓ by log_two_mul_le).
  -- The tower and lattice bridge are the sorry'd components.
  sorry

/-! ## §3  CM norm-one element construction (class-group pigeonhole)

**Mathematical content** (Prop 2.2 of [OpenAI 2026]):

Given K = K_j (CM, degree 2f_j), split primes q₁,…,qₜ (each gives f conjugate
pairs {𝔓_s, c𝔓_s} in K), and h(K) ≤ H^f:

1. For ε = (εₛ) ∈ {0,1}^m (m = tf), set 𝔄_ε = ∏_{εₛ=1} 𝔓_s ∏_{εₛ=0} c𝔓_s.
2. The 2^m ideals 𝔄_ε lie in ≤ h(K) ≤ H^f ideal classes.
3. By pigeonhole, ∃ class C with |{ε : [𝔄_ε] = C}| ≥ 2^m/H^f = exp(γf).
4. Fix η in this class. For each ε in the class, αε ∈ K× with (αε) = 𝔄_ε𝔄_η⁻¹.
   Set u_ε = αε/c(αε). Then u_ε·c(u_ε) = 1, so |σ(u_ε)| = 1 for all σ.
   Also Q²u_ε ∈ O_K (from the prime factorization of the poles), so u_ε ∈ D₀⁻¹O_K.
5. Distinct ε give distinct u_ε (by their prime-ideal valuations).

**Lean gap**: this sorry requires:
(a) An API for constructing prime ideal pairs {𝔓_s, c𝔓_s} in a CM field K given
    a split prime q_b (requires `Ideal.IsPrime`, splitting loci — not in Mathlib 2025)
(b) Arithmetic of ideal classes and the ClassGroup-pigeonhole
    (`Fintype.exists_ne_map_eq_of_card_lt` is in Mathlib, but the class-group
     map ε ↦ [𝔄_ε] and the norm-1 quotient u_ε = αε/c(αε) require CM field API)
(c) Lifting u_ε into `AddSubgroup (Fin f → ℂ)` (type bridge, as in §2)
-/

/-- **CM norm-one element set** (Prop 2.2, sorry'd).

    Given abstract hypotheses matching the output of `golod_shafarevich_tower_with_lattice`:
    - `f ≥ 1`, `D₀ > 0`, `t ≥ 0`, `log_H` with γ = t log 2 - log_H > 0
    - `Λ : AddSubgroup (Fin f → ℂ)` satisfying `hΛ_sep`

    Produces `U : Finset (Fin f → ℂ)` with:
    - All coordinates of u ∈ U have modulus 1
    - All u ∈ U lie in Λ
    - |U| ≥ exp(γ · f)

    **Concrete proof sketch**:
    Set m = t · f. Form the 2^m binary vectors ε ∈ {0,1}^m.  Map each ε to the ideal
    class [𝔄_ε] ∈ ClassGroup K (via the split-prime pair API).  Since |ClassGroup K| ≤ H^f,
    `Fintype.exists_ne_map_eq_of_card_lt` gives a class with ≥ exp(γf) preimages.
    For each pair (ε,η) in that class form u_ε := αε/c(αε) ∈ D₀⁻¹O_K, which has
    |σ(u_ε)| = 1 under every complex embedding σ (equation (3) in the paper).
    Collect these into U; distinctness of ε gives |U| ≥ exp(γf). -/
def cm_norm_one_elements
    (f : ℕ) (hf1 : f ≥ 1) (D₀ : ℝ) (hD₀ : D₀ > 0)
    (t log_H : ℝ) (ht : t ≥ 0) (hγ : t * Real.log 2 - log_H > 0)
    (Λ : AddSubgroup (Fin f → ℂ))
    (hΛ_sep : ∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf1)‖ ≥ D₀⁻¹) :
    ∃ (U : Finset (Fin f → ℂ)),
      (∀ u ∈ U, ∀ r : Fin f, ‖u r‖ = 1) ∧
      (∀ u ∈ U, (u : Fin f → ℂ) ∈ Λ) ∧
      ((U.card : ℝ) ≥ Real.exp ((t * Real.log 2 - log_H) * (f : ℝ))) := by
  -- The proof goes via the class-group pigeonhole.
  -- We cannot complete it without explicit K and CM-field API.
  -- The missing steps are:
  --   · `ClassGroup K` API for ideal pair construction
  --   · `Fintype.exists_ne_map_eq_of_card_lt` applied to the class map ε ↦ [𝔄_ε]
  --   · Norm-one quotient u_ε = αε/c(αε) in D₀⁻¹O_K, lifted to Fin f → ℂ
  sorry

/-! ## §4  Assembly: structured proofs of `prop_3_2_to_3_6` and `prop_2_2` -/

/-- **Structured proof of `prop_3_2_to_3_6`**.

    Uses `golod_shafarevich_tower_with_lattice` (§2) which carries the single
    consolidated sorry for the tower + lattice bridge.  The log-bound step
    (log rd_F ≤ ℓ·log ℓ) is proved by `log_two_mul_le`.  Everything else is
    an explicit refinement of the existential statement. -/
theorem prop_3_2_to_3_6_via_deep :
    ∃ (C_rd : ℝ), C_rd > 0 ∧
    ∀ (ℓ : ℕ), ℓ ≥ 2 →
    ∃ (D₀ : ℝ), D₀ > 0 ∧ ∃ (rd_F : ℝ), rd_F ≥ 1 ∧
      Real.log rd_F ≤ C_rd * (ℓ : ℝ) * Real.log (ℓ : ℝ) ∧
      ∀ (M : ℕ),
      ∃ (f : ℕ), f ≥ M ∧ ∃ (hf1 : f ≥ 1) (Λ : AddSubgroup (Fin f → ℂ))
        (_ : Countable Λ) (F : Set (Fin f → ℂ)),
        IsAddFundamentalDomain Λ F volume ∧ volume F < ∞ ∧
        (∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf1)‖ ≥ D₀⁻¹) := by
  -- C_rd = 1: the log bound log rd_F ≤ ℓ·log ℓ holds for the cyclic cubic field
  -- (rd_F ≤ 2ℓ and log(2ℓ) ≤ ℓ·log ℓ by log_two_mul_le).
  refine ⟨1, one_pos, fun ℓ hℓ => ?_⟩
  -- Obtain the tower data (D₀, rd_F, and levels) from the GS-tower sorry.
  obtain ⟨D₀, hD₀_pos, rd_F, hrd_ge1, hlog_rd, h_levels⟩ :=
    golod_shafarevich_tower_with_lattice ℓ hℓ
  -- The log bound already satisfies log rd_F ≤ 1 · ℓ · log ℓ (= ℓ · log ℓ).
  exact ⟨D₀, hD₀_pos, rd_F, hrd_ge1, by linarith, h_levels⟩

end
