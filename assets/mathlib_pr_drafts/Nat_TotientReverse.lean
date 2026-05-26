/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Algebra.Ring.Parity
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Reverse totient inequality

For any natural number `n`, `n ≤ 4 · (Nat.totient n) ^ 2`.

This complements the existing `Nat.totient_le n : Nat.totient n ≤ n` by giving
a polynomial reverse inequality.

The proof uses an odd helper (`Nat.Odd.le_totient_sq`) combined with the 2-adic
decomposition `n = 2^a · m` via `padicValNat 2 n`.

## Main definitions and results

* `Nat.Odd.le_totient_sq`: for any odd `m`, `m ≤ φ(m)²`.
* `Nat.le_four_mul_totient_sq`: for any `n`, `n ≤ 4 · φ(n)²`.

## Mathematical content

For odd m: by strong induction via `Nat.recOnPosPrimePosCoprime`.
- Prime power case (odd prime p ≥ 3): direct algebra.
- Coprime case: multiplicativity of φ plus the inductive hypotheses.

For general n: decompose n = 2^a · m, apply odd helper to m.
- a = 0 (n odd): direct from odd helper.
- a ≥ 1: φ(n) = 2^(a-1) · φ(m), and the bound chains using
  `2^a · m ≤ 4 · (2^(a-1))² · φ(m)²` ⟺ `m ≤ 2^a · φ(m)²` (which holds for
  odd m by the helper + 2^a ≥ 2).

This is a Mathlib PR candidate extracted from the
[Erd46 formalization](https://github.com/.../erd46).
-/

namespace Nat

/-- For any odd natural number `m`, `m ≤ φ(m)²`.

Proof by strong induction via `Nat.recOnPosPrimePosCoprime`. -/
lemma Odd.le_totient_sq : ∀ (m : ℕ), Odd m → m ≤ m.totient ^ 2 := by
  refine Nat.recOnPosPrimePosCoprime ?_ ?_ ?_ ?_
  -- prime_pow case: p prime, 0 < k, Odd (p^k)
  · intro p k hp hk hm_odd
    -- Odd (p^k) with k ≥ 1 ⟹ Odd p ⟹ p ≥ 3
    have hp_odd : Odd p := (Nat.odd_pow_iff hk.ne').mp hm_odd
    have hp_ge3 : 3 ≤ p := by
      have hp2 : 2 ≤ p := hp.two_le
      rcases hp2.lt_or_eq with h | h
      · omega
      · exfalso
        rw [← h] at hp_odd
        exact (Nat.not_odd_iff_even.mpr (by decide)) hp_odd
    rw [Nat.totient_prime_pow hp hk]
    rcases (Nat.lt_or_ge 1 k) with hk_ge2 | hk_le1
    · -- k ≥ 2
      have h_exp : (k - 1) * 2 = k + (k - 2) := by omega
      have h_pow_eq : (p ^ (k - 1)) ^ 2 = p ^ k * p ^ (k - 2) := by
        rw [← pow_mul, h_exp, pow_add]
      rw [Nat.mul_pow, h_pow_eq]
      have h_p1_sq : 1 ≤ (p - 1) ^ 2 := by
        have : 2 ≤ p - 1 := by omega
        nlinarith
      have h_pkm2 : 1 ≤ p ^ (k - 2) := Nat.one_le_iff_ne_zero.mpr <| by positivity
      calc p ^ k = p ^ k * 1 := by ring
        _ ≤ p ^ k * (p ^ (k - 2) * (p - 1) ^ 2) :=
            Nat.mul_le_mul_left _ (by nlinarith)
        _ = p ^ k * p ^ (k - 2) * (p - 1) ^ 2 := by ring
    · -- k = 1
      have hk1 : k = 1 := by omega
      subst hk1
      simp only [pow_one, Nat.sub_self, pow_zero, one_mul]
      have hpm1 : 2 ≤ p - 1 := by omega
      calc p = (p - 1) + 1 := by omega
        _ ≤ 2 * (p - 1) := by omega
        _ ≤ (p - 1) * (p - 1) := Nat.mul_le_mul_right (p - 1) hpm1
        _ = (p - 1) ^ 2 := by ring
  -- zero case: Odd 0 → 0 ≤ 0².  Vacuous.
  · intro hm; exact absurd hm (by decide)
  -- one case: Odd 1 → 1 ≤ 1².  Trivial.
  · intro _; decide
  -- coprime case: a, b > 1 coprime, with IH, Odd (a*b)
  · intro a b _ _ hab IHa IHb hm_odd
    have h_mul := Nat.odd_mul.mp hm_odd
    have ha_odd : Odd a := h_mul.1
    have hb_odd : Odd b := h_mul.2
    rw [Nat.totient_mul hab]
    calc a * b ≤ a.totient ^ 2 * b.totient ^ 2 :=
          Nat.mul_le_mul (IHa ha_odd) (IHb hb_odd)
      _ = (a.totient * b.totient) ^ 2 := by ring

/-- **Reverse totient inequality**: for any natural number `n`,
`n ≤ 4 · (Nat.totient n)²`.

Proof: case n ≤ 16 by direct computation, n ≥ 17 by 2-adic decomposition
`n = 2^a · m` (with m odd) and `Nat.Odd.le_totient_sq` applied to m. -/
lemma le_four_mul_totient_sq (n : ℕ) : n ≤ 4 * n.totient ^ 2 := by
  by_cases hn : n ≤ 16
  · interval_cases n <;> decide
  · push_neg at hn
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set a := padicValNat 2 n with ha_def
    set m := n / 2 ^ a with hm_def
    have hn_pos : 0 < n := by omega
    have hn_ne_zero : n ≠ 0 := hn_pos.ne'
    have h_pa_dvd : 2 ^ a ∣ n := pow_padicValNat_dvd
    have hn_eq : n = 2 ^ a * m := by
      rw [hm_def, Nat.mul_div_cancel' h_pa_dvd]
    have h_two_pos : (0 : ℕ) < 2 := by norm_num
    have h_2pow_pos : (0 : ℕ) < 2 ^ a := pow_pos h_two_pos a
    have h_m_pos : 0 < m := by
      rw [hm_def]
      exact Nat.div_pos (Nat.le_of_dvd hn_pos h_pa_dvd) h_2pow_pos
    have hm_odd : Odd m := by
      rw [← Nat.not_even_iff_odd]
      intro h_even
      have h2dvd : 2 ∣ m := h_even.two_dvd
      have h_pow_succ_dvd : 2 ^ (a + 1) ∣ n := by
        rw [hn_eq, pow_succ]
        exact mul_dvd_mul (dvd_refl _) h2dvd
      exact pow_succ_padicValNat_not_dvd hn_ne_zero h_pow_succ_dvd
    have h_m_le : m ≤ m.totient ^ 2 := Nat.Odd.le_totient_sq m hm_odd
    have h_coprime : Nat.Coprime (2 ^ a) m := by
      have h_m_two : Nat.Coprime 2 m := (Nat.coprime_two_left).mpr hm_odd
      exact Nat.Coprime.pow_left a h_m_two
    have h_totient_n : n.totient = (2 ^ a).totient * m.totient := by
      rw [hn_eq, Nat.totient_mul h_coprime]
    rcases Nat.eq_zero_or_pos a with ha0 | ha_pos
    · -- a = 0
      have hn_odd : n = m := by rw [hn_eq, ha0, pow_zero, one_mul]
      rw [hn_odd]
      linarith [h_m_le]
    · -- a ≥ 1
      have h_phi_2pow : (2 ^ a).totient = 2 ^ (a - 1) := by
        rw [Nat.totient_prime_pow Nat.prime_two ha_pos]; ring
      rw [h_totient_n, h_phi_2pow]
      rw [hn_eq]
      have h_2pow_split : 2 ^ a = 2 * 2 ^ (a - 1) := by
        conv_lhs => rw [show a = (a - 1) + 1 from by omega]
        ring
      have h_2pow_a_sq : 4 * (2 ^ (a - 1)) ^ 2 = (2 ^ a) ^ 2 := by
        rw [h_2pow_split]; ring
      calc 2 ^ a * m ≤ 2 ^ a * m.totient ^ 2 :=
            Nat.mul_le_mul_left _ h_m_le
        _ ≤ (2 ^ a) ^ 2 * m.totient ^ 2 := by
            have : 2 ^ a ≤ (2 ^ a) ^ 2 := by
              have h1 : 1 ≤ 2 ^ a := Nat.one_le_iff_ne_zero.mpr h_2pow_pos.ne'
              nlinarith
            exact Nat.mul_le_mul_right _ this
        _ = 4 * (2 ^ (a - 1)) ^ 2 * m.totient ^ 2 := by rw [← h_2pow_a_sq]
        _ = 4 * (2 ^ (a - 1) * m.totient) ^ 2 := by ring

end Nat
