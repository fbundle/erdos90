import Mathlib
import Erd46.Defs
import Erd46.Arithmetic
import Erd46.Geometric

/-!
# Theorem 1.1: The Erdős unit-distance conjecture is false (for human verification)

We prove that there exists an absolute constant δ > 0 and infinitely many
positive integers n such that ν(n) ≥ n^{1+δ}.

This follows from the existence of admissible families (Arithmetic.lean)
and the geometric construction (Geometric.lean).
-/

/-! ## Theorem 1.1: The Erdős unit-distance conjecture is false -/

open Real

/-- Any finite planar point set P achieves ν(P) ≤ maxUnitDists(|P|), since
    maxUnitDists is defined as the supremum over all n-point configurations. -/
lemma unitDistPairs_le_maxUnitDists (P : Finset (ℝ × ℝ)) :
    unitDistPairs P ≤ maxUnitDists P.card := by
  apply le_csSup
  · refine ⟨P.card ^ 2, ?_⟩
    rintro k ⟨Q, hQcard, rfl⟩
    simp only [unitDistPairs]
    have h1 : ((Q.offDiag).filter (fun x => distSq x.1 x.2 = 1)).card ≤ Q.card ^ 2 := by
      calc ((Q.offDiag).filter (fun x => distSq x.1 x.2 = 1)).card
          ≤ Q.offDiag.card := Finset.card_filter_le _ _
        _ ≤ (Q ×ˢ Q).card := by
            apply Finset.card_le_card
            intro x hx
            exact Finset.mem_product.mpr ⟨(Finset.mem_offDiag.mp hx).1,
              (Finset.mem_offDiag.mp hx).2.1⟩
        _ = Q.card ^ 2 := by simp [Finset.card_product]; ring
    calc ((Q.offDiag).filter (fun x => distSq x.1 x.2 = 1)).card / 2
        ≤ ((Q.offDiag).filter (fun x => distSq x.1 x.2 = 1)).card := Nat.div_le_self _ _
      _ ≤ Q.card ^ 2 := h1
      _ = P.card ^ 2 := by rw [hQcard]
  · exact ⟨P, rfl, rfl⟩

/-- **Theorem 1.1.**  There exists δ > 0 such that ν(n) ≥ n^{1+δ}
    for infinitely many n.

    Proof outline:
    1. By the arithmetic axiom, there exists γ > 0, D > 0 and, for arbitrarily
       large f, an `AdmissibleFamily` A_f with A_f.γ = γ and A_f.D = D.
    2. Fix R > 1/2 via the ρ-axiom such that log ρ(R) > -γ/2 and 4RD > 1.
       Set δ = γ/(8·log(4RD)) > 0.  Note δ depends only on γ, D, R, not on f.
    3. For large enough f, `planar_set_from_datum` gives a planar set P_f with
       - |P_f| ≥ exp(γ/2 · f), so |P_f| → ∞ as f → ∞
       - ν(P_f) ≥ ½ · exp(γ/2 · f) · |P_f| ≥ ½ · |P_f|^{2δ} · |P_f| = ½ · |P_f|^{1+2δ}
         (using |P_f| ≤ exp(B·f) so exp(γ/2·f) ≥ |P_f|^{γ/(2B)} = |P_f|^{2δ})
    4. For |P_f|^δ ≥ 2 (large f), ½ · |P_f|^{1+2δ} ≥ |P_f|^{1+δ}.
    5. Setting n_f = |P_f| gives arbitrarily large n with ν(n) ≥ n^{1+δ}. -/
theorem erdos_unit_distance_false :
    ∃ (δ : ℝ), δ > 0 ∧ (∀ N : ℕ, ∃ n ≥ N, (maxUnitDists n : ℝ) ≥ (n : ℝ) ^ (1 + δ)) := by
  -- Step 1: obtain the uniform constants γ > 0, D > 0 and the tower
  obtain ⟨γ, hγ_pos, D, hD_pos, h_tower⟩ := exists_admissible_family
  -- Step 2: fix R > 1/2 via the ρ-axiom; log ρ(R) > -γ/2 and 4RD > 1
  have hγ2_pos : γ / 2 > 0 := half_pos hγ_pos
  obtain ⟨R, hR, hρ_global, h_4RD_gt_one⟩ := exists_R_log_rho_gt (γ / 2) hγ2_pos D hD_pos
  -- Step 3: define δ = γ/(4B) where B = 2·log(4RD); this is independent of f
  set B := 2 * Real.log (4 * R * D) with hB_def
  have hB_pos : B > 0 := by
    have hlog : Real.log (4 * R * D) > 0 := Real.log_pos h_4RD_gt_one
    positivity
  set δ := γ / (4 * B) with hδ_def
  have hδ_pos : δ > 0 := div_pos hγ_pos (by positivity)
  have h_γ_over_2_eq_2δB : γ / 2 = 2 * δ * B := by
    rw [hδ_def]; field_simp [show B ≠ 0 from by linarith [hB_pos]]; ring
  refine ⟨δ, hδ_pos, fun N => ?_⟩
  -- Step 4: choose M so that for any A with A.f ≥ M:
  --   exp(γ/2 * A.f) ≥ N  (ensures |P| ≥ N)
  --   exp(γ/2 * δ * A.f) ≥ 2  (ensures |P|^δ ≥ 2 for the final rpow step)
  let M : ℕ := max (⌈Real.log N / (γ / 2)⌉₊) (⌈Real.log 2 / (γ / 2 * δ)⌉₊)
  obtain ⟨A, hAf, hAγ, hAD⟩ := h_tower M
  -- Step 5: apply planar_set_from_datum with R fixed
  have hρ_A : Real.log (rho R) > -(A.γ / 2) := by rw [hAγ]; exact hρ_global
  have h4RD_A : 4 * R * A.D > 1 := by rw [hAD]; exact h_4RD_gt_one
  obtain ⟨P, hP_ge1, h_P_lower, h_P_upper, h_edges_lower⟩ :=
    planar_set_from_datum A R hR hρ_A h4RD_A
  -- Rewrite A.γ and A.D using the tower equalities
  have hAγ_eq : A.γ / 2 * (A.f : ℝ) = γ / 2 * (A.f : ℝ) := by rw [hAγ]
  have hAD_eq : 2 * Real.log (4 * R * A.D) = B := by rw [hAD, hB_def]
  have h_P_lower' : (P.card : ℝ) ≥ Real.exp (γ / 2 * (A.f : ℝ)) := by rwa [← hAγ_eq]
  have h_P_upper' : (P.card : ℝ) ≤ Real.exp (B * (A.f : ℝ)) := by
    have h := h_P_upper; rwa [hAD_eq] at h
  have h_edges_lower' : (unitDistPairs P : ℝ) ≥
      (1/2 : ℝ) * Real.exp (γ / 2 * (A.f : ℝ)) * (P.card : ℝ) := by
    rwa [← hAγ_eq]
  have hPcard_pos : (P.card : ℝ) > 0 := by
    exact_mod_cast Nat.pos_of_ne_zero (by omega)
  -- Step 6: show |P| ≥ N via |P| ≥ exp(γ/2·A.f) ≥ exp(γ/2·M) ≥ N
  have h_Pcard_ge_N : P.card ≥ N := by
    have h : (N : ℝ) ≤ (P.card : ℝ) := ?_
    · exact_mod_cast h
    have hMle : (M : ℝ) ≥ ⌈Real.log N / (γ / 2)⌉₊ := by exact_mod_cast Nat.le_max_left _ _
    have hAfMle : (A.f : ℝ) ≥ (M : ℝ) := by exact_mod_cast hAf
    have h_exp_N_le : (N : ℝ) ≤ Real.exp (γ / 2 * (M : ℝ)) := by
      rcases Nat.eq_zero_or_pos N with rfl | hN_pos
      · simp; positivity
      have hNr : (N : ℝ) > 0 := Nat.cast_pos.mpr hN_pos
      rw [← Real.log_le_iff_le_exp hNr]
      calc Real.log N = Real.log N / (γ / 2) * (γ / 2) := by field_simp
        _ ≤ (M : ℝ) * (γ / 2) := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            calc Real.log N / (γ / 2) ≤ ⌈Real.log N / (γ / 2)⌉₊ := Nat.le_ceil _
              _ ≤ (M : ℝ) := hMle
        _ = γ / 2 * (M : ℝ) := by ring
    calc (N : ℝ) ≤ Real.exp (γ / 2 * (M : ℝ)) := h_exp_N_le
      _ ≤ Real.exp (γ / 2 * (A.f : ℝ)) := by
          apply Real.exp_le_exp.mpr; gcongr
      _ ≤ (P.card : ℝ) := h_P_lower'
  -- Step 7: exp(γ/2·f) ≥ |P|^{2δ} via size upper bound
  have h_exp_bound : Real.exp (γ / 2 * (A.f : ℝ)) ≥ (P.card : ℝ) ^ (2 * δ) := by
    rw [Real.rpow_def_of_pos hPcard_pos]
    apply Real.exp_le_exp.mpr
    have hlog_le : Real.log (P.card : ℝ) ≤ B * (A.f : ℝ) := by
      have h := Real.log_le_log hPcard_pos h_P_upper'
      rwa [Real.log_exp] at h
    calc Real.log (P.card : ℝ) * (2 * δ)
        ≤ B * (A.f : ℝ) * (2 * δ) := mul_le_mul_of_nonneg_right hlog_le (by positivity)
      _ = γ / 2 * (A.f : ℝ) := by rw [h_γ_over_2_eq_2δB]; ring
  -- Step 8: |P|^δ ≥ 2 from |P| ≥ exp(γ/2·A.f) ≥ exp(γ/2·δ·M) ≥ 2
  have h_Pcard_δ : (P.card : ℝ) ^ δ ≥ 2 := by
    have hMle2 : (M : ℝ) ≥ ⌈Real.log 2 / (γ / 2 * δ)⌉₊ := by exact_mod_cast Nat.le_max_right _ _
    have hAfMle : (A.f : ℝ) ≥ (M : ℝ) := by exact_mod_cast hAf
    calc (P.card : ℝ) ^ δ
        ≥ Real.exp (γ / 2 * (A.f : ℝ)) ^ δ :=
          Real.rpow_le_rpow (Real.exp_nonneg _) h_P_lower' (le_of_lt hδ_pos)
      _ = Real.exp (γ / 2 * δ * (A.f : ℝ)) := by
          rw [← Real.exp_mul]; ring_nf
      _ ≥ Real.exp (γ / 2 * δ * (M : ℝ)) := by
          apply Real.exp_le_exp.mpr; gcongr
      _ ≥ 2 := by
          rw [ge_iff_le, ← Real.log_le_iff_le_exp (by norm_num)]
          calc Real.log 2 = Real.log 2 / (γ / 2 * δ) * (γ / 2 * δ) := by field_simp
            _ ≤ (M : ℝ) * (γ / 2 * δ) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                calc Real.log 2 / (γ / 2 * δ) ≤ ⌈Real.log 2 / (γ / 2 * δ)⌉₊ := Nat.le_ceil _
                  _ ≤ (M : ℝ) := hMle2
            _ = γ / 2 * δ * (M : ℝ) := by ring
  -- Step 9: ν(P) ≥ ½·|P|^{1+2δ} ≥ |P|^{1+δ}
  have h_final : (unitDistPairs P : ℝ) ≥ (P.card : ℝ) ^ (1 + δ) := by
    calc (unitDistPairs P : ℝ)
        ≥ (1/2 : ℝ) * Real.exp (γ / 2 * (A.f : ℝ)) * (P.card : ℝ) := h_edges_lower'
      _ ≥ (1/2 : ℝ) * ((P.card : ℝ) ^ (2 * δ)) * (P.card : ℝ) := by gcongr
      _ = (1/2 : ℝ) * ((P.card : ℝ) ^ (1 + 2 * δ)) := by
          rw [show (1 : ℝ) + 2 * δ = 2 * δ + 1 from by ring,
              Real.rpow_add hPcard_pos, Real.rpow_one]; ring
      _ ≥ (P.card : ℝ) ^ (1 + δ) := by
          rw [show (1 : ℝ) + 2 * δ = (1 + δ) + δ from by ring,
              Real.rpow_add hPcard_pos]
          nlinarith [Real.rpow_nonneg (by linarith : (P.card : ℝ) ≥ 0) (1 + δ)]
  -- Step 10: conclude ν(P.card) ≥ P.card^{1+δ} and P.card ≥ N
  exact ⟨P.card, h_Pcard_ge_N, by
    calc (maxUnitDists P.card : ℝ)
        ≥ (unitDistPairs P : ℝ) := Nat.cast_le.mpr (unitDistPairs_le_maxUnitDists P)
      _ ≥ (P.card : ℝ) ^ (1 + δ) := h_final⟩

/-- **Equivalent formulation**: the Erdős bound is false.
    There do not exist C > 0 and N ∈ ℕ such that
    ν(n) ≤ n^{1 + C/log log n} for all n ≥ N.

    Proof: From Theorem 1.1, ν(n) ≥ n^{1+δ} for arbitrarily large n.
    The Erdős bound would require n^{1+δ} ≤ n^{1 + C/log log n},
    i.e., δ ≤ C/log log n.  But log log n → ∞ as n → ∞, so for
    n > exp(exp(C/δ)) this inequality is reversed, a contradiction. -/
theorem erdos_bound_false :
    ¬ ∃ (C : ℝ) (N : ℕ), C > 0 ∧ (∀ n ≥ N, (maxUnitDists n : ℝ) ≤ (n : ℝ) ^ (1 + C / Real.log (Real.log (n : ℝ)))) := by
  -- Suppose the Erdős bound holds for some C > 0, N
  rintro ⟨C, N, hC_pos, h_bound⟩
  -- From Theorem 1.1, we have δ > 0 with ν(n) ≥ n^{1+δ} for infinitely many n
  obtain ⟨δ, hδ_pos, h_inf⟩ := erdos_unit_distance_false
  -- We need n large enough that:
  -- (a) n ≥ N (to apply the Erdős bound)
  -- (b) log(log n) > C/δ (to derive a contradiction)
  -- Since log log n → ∞, both hold for sufficiently large n.
  -- Let n be from Theorem 1.1 with n ≥ max(N, ceil(exp(exp(C/δ))) + 1).
  --
  -- Then: n^{1+δ} ≤ ν(n) ≤ n^{1 + C/log log n}
  -- Taking log: (1+δ)·log n ≤ (1 + C/log log n)·log n
  -- So δ ≤ C/log log n, i.e., log log n ≤ C/δ
  -- But by construction log(log n) > C/δ, contradiction.
  --
  -- Formalizing this requires the real log/exp monotonicity and the
  -- asymptotic of log log n → ∞.  Left as `sorry` for now.
  sorry
