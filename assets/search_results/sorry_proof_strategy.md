# Proof Strategy for the Three Remaining Sorries

Source: OpenAI paper (unit-distance-proof.pdf), Sawin paper (arXiv:2605.20579), Mathlib audit

Last updated: 2026-05-25

---

## Summary

There are 3 sorries in `exists_cm_class_group_data` in `Erdos90/NumberFieldDeep_CM.lean`:

| Sorry | Lines | What's needed |
|-------|-------|----------------|
| `h_card_ratio` | 489-494 | Minkowski class-number bound: h(K) ≤ H^f |
| `hmk_unit_mem_Λ` | 571-573 | Integrality: Q²·(α/c(α)) ∈ 𝓞_K |
| `hmk_unit_inj` | 593-656 | Injectivity via valuation vectors |

All three require the same core missing Mathlib API: **valuation of an element at a specific prime ideal** (`IsDedekindDomain.HeightOneSpectrum.valuation`), and specifically:
1. Computing the valuation of α from the ideal equation (α) = 𝔄_ε · 𝔄_η⁻¹
2. The formula v_{𝔓_s}(c(α)) = v_{c𝔓_s}(α) (conjugation swaps valuations)
3. The formula v_{𝔓}(∏ 𝔓_i^{e_i}) = e_j for 𝔓 = 𝔓_j (factorization of ideals)

---

## Sorry 1: `h_card_ratio` (line 494)

### Mathematical statement
```
exp((t·log 2 − log_H)·f) + 1 ≤ (2^m : ℝ) / cardG
```
where m = t'·f ≥ t·f, cardG = h(K) ≤ H^f (class number bound).

### Paper source
Proposition 3.7 (page 12) + Proposition A.13 (page 16):
```
h(K) ≤ max{2, rd(K)}^{C_class · [K:ℚ]}
```
Applied with rd(K_j) ≤ 2rd(F), log rd(F) = O(ℓ log ℓ), [K_j:ℚ] = 2f_j.

### External references
- [Neu99, Chapter I, Section 5]: Minkowski's bound + counting ideals of bounded norm
- [Lan94, Chapter V]: Alternative exposition

### Lean strategy (two options)

**Option A** (preferred, short-circuit the bound):
The `log_H` and `t` parameters in `exists_cm_class_group_data` are already inputs from `gs_tower_levels`, which provides the bound h(K) ≤ H_ℓ^{f_j}. The current `h_card_ratio` sorry is a purely numerical consequence of those inputs: need `2^m / cardG ≥ exp(γf) + 1` given `m ≥ tf` and `cardG ≤ H^f`. This is:
```
2^{tf} / H^f = (2^t / H)^f = exp((t·log 2 − log H)·f)
```
So the `sorry` reduces to: given `t * Real.log 2 > log_H` (which is `hγ : γ > 0` + `γ = t·log 2 − log_H`), prove `exp((t·log 2 − log_H)·f) + 1 ≤ (2^m)^f / H^f`.

**Key subgoal**: `(cardG : ℝ) ≤ Real.exp (log_H * f)`. This is `cardG ≤ H^f` (the class number bound from the GS tower data). It may already be passed as `hcardG : cardG ≤ ...` — check the `CMClassGroupData` structure fields.

**Option B** (add helper sorry): Add a dedicated sorry'd lemma `class_number_le_exp_log_H_mul_f` that states this bound, and use it.

---

## Sorry 2: `hmk_unit_mem_Λ` (line 573)

### Mathematical statement
```
(α / IsCMField.complexConj K α) ∈ (algebraMap (𝓞 K) K).range
```
i.e., α/c(α) ∈ 𝓞_K (as an element of K).

**Note**: This is with D₀ = 1 (current tower). The full paper uses D₀ = Q², and proves u_ε ∈ Q^{-2}𝓞_K = Λ. With D₀ = 1, u_ε ∈ Λ = 𝓞_K only if α/c(α) is integral, which requires the denominators at split primes to cancel — this only holds if valuation exponents are all ≥ 0.

### Correct statement (paper, page 7)
The principal ideal of u_ε = α_ε/c(α_ε) satisfies:
```
v_{𝔓_s}(u_ε) = 2(ε_s − η_s)  ∈ {-2, 0, 2}
v_{c𝔓_s}(u_ε) = -2(ε_s − η_s)
```
Since Q = ∏_{b=1}^t q_b and q_b𝓞_K has valuation 1 at each 𝔓_s over q_b:
```
v_{𝔓_s}(Q) = 1
v_{𝔓_s}(Q²·u_ε) = 2 + 2(ε_s − η_s) ≥ 0
```
So Q²·u_ε ∈ 𝓞_K, i.e., u_ε ∈ Q^{-2}𝓞_K.

### What the Lean code currently needs
The Lean code has `Λ = cmData.Λ` and calls `mk_unit_from_cm_quotient`, which needs `α/c(α) ∈ (algebraMap (𝓞 K) K).range`. But this is only true when D₀ = Q² and Λ = Q^{-2}𝓞_K — not with D₀ = 1.

### Fix needed
**Either** update the `CMClassGroupData` structure to use Λ = Q^{-2}𝓞_K and update `mk_unit_from_cm_quotient` accordingly, **or** sorry the integrality claim and document that it requires the D₀ = Q² tower.

The simplest path for now: keep the sorry with a clear comment that it requires D₀ = Q² (i.e., D₀ = (∏_{b=1}^t q_b)²), and document that closing this sorry requires:
1. The `SplitPrimeData` to provide the valuation formula v_{𝔓_s}(𝔄_ε) = ε_s
2. A Mathlib lemma for valuation of a product ideal: `val_prod_eq_sum_val`
3. The conjugation-swapping formula: `val_conj_swap`

### Missing Mathlib API for this sorry
```lean
-- Formula v(I · J) = v(I) + v(J) for fractional ideals
IsDedekindDomain.HeightOneSpectrum.valuation_mul :
    v.valuation K (x * y) = v.valuation K x * v.valuation K y  -- in ℤᵐ⁰

-- Formula v_{c𝔓}(α) = v_{𝔓}(c(α)) (Galois-equivariance of valuations)
-- Statement: for σ : K →ₐ[ℚ] K an automorphism, v_{σ𝔓}(α) = v_{𝔓}(σ⁻¹ α)
-- NOT in Mathlib; needs to be added or sorried
```

---

## Sorry 3: `hmk_unit_inj` (line 656)

### Mathematical statement
```
mk_unit ε₁ ε₂ = mk_unit ε₁ ε₃ → ε₂ = ε₃
```
where `mk_unit ε₁ ε₂ = cmData.φ (mixedEmbedding K (α₂ / c(α₂)))` and α₂ is chosen with (α₂) = J(ε₂) · J(ε₁)^{-1}.

### Current Lean proof structure (lines 593-656)
The code already proves:
1. **Step 1** (lines 603-610): Minkowski injectivity → α₂/c(α₂) = α₃/c(α₃) in K
2. **Step 2** (lines 611-638): Algebraic manipulation → α₂/α₃ is fixed by c → α₂/α₃ ∈ K⁺

The sorry at line 656 is **Step 4 (Lemma B)**: α₂/α₃ ∈ K⁺ ∧ ideal equations → ε₂ = ε₃.

### Paper's direct argument (simpler)
Paper equation (4): v_{𝔓_s}(u_{ε_i}) = 2(ε_s^{(i)} − η_s). So:
```
u_{ε₂} = u_{ε₃} → v_{𝔓_s}(u_{ε₂}) = v_{𝔓_s}(u_{ε₃}) → ε₂_s − η_s = ε₃_s − η_s → ε₂_s = ε₃_s
```

### Lean's indirect argument (what the sorry needs)
Given α₂/α₃ ∈ K⁺ and (α₂)·J(ε₁) = J(ε₂), (α₃)·J(ε₁) = J(ε₃):
- (α₂/α₃) = J(ε₂)/J(ε₃) as fractional ideals
- For each s: v_{𝔓_s}(α₂/α₃) = v_{𝔓_s}(J(ε₂)) − v_{𝔓_s}(J(ε₃)) = ε₂_s − ε₃_s
- Since α₂/α₃ ∈ K⁺: v_{𝔓_s}(α₂/α₃) = v_{c𝔓_s}(α₂/α₃) (K⁺-elements have equal valuation at conjugate primes)
- But v_{c𝔓_s}(α₂/α₃) = -(ε₂_s − ε₃_s) (conjugate primes get negated exponents)
- So ε₂_s − ε₃_s = -(ε₂_s − ε₃_s), giving ε₂_s = ε₃_s

### Missing Mathlib API (same as Sorry 2)
The key missing fact is: **for β ∈ K⁺, v_{𝔓}(β) = v_{c𝔓}(β)**.

This is a general fact about totally real subfields: if β ∈ K⁺ = maximalRealSubfield K, and 𝔓 is a prime of K lying over a prime 𝔭 of K⁺, then c(𝔓) also lies over 𝔭, and since 𝔭𝓞_K = 𝔓·c(𝔓) (split prime), the valuations of β ∈ K⁺ at 𝔓 and c(𝔓) are equal (both equal v_{𝔭}(β) after restriction to K⁺).

---

## Recommended Search for Related Mathlib PRs

Search Lean4 Zulip / GitHub for:
1. `IsDedekindDomain.HeightOneSpectrum.valuation_congr` or similar Galois-equivariance
2. `Ideal.LiesOver` + valuation compatibility
3. PRs mentioning "adic valuation" + "Galois" or "automorphism"
4. `IsDedekindDomain.HeightOneSpectrum.algebraMap_valuation` — relating element valuation to ideal valuation

## Recommended Helper Lemmas to Sorry

To close all three sorries with minimal effort, add these sorried helpers:

```lean
-- Helper A: valuation of conjugate element
lemma valuation_complexConj (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hv : v.asIdeal = conjIdeal K v'.asIdeal)
    (α : K) :
    v.valuation K α = v'.valuation K (IsCMField.complexConj K α) := by
  sorry -- Galois-equivariance of adic valuation; [Neu99, I.8.3]

-- Helper B: K⁺-elements have equal valuation at conjugate primes
lemma valuation_eq_conj_of_mem_maxReal (v v' : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hconj : v'.asIdeal = conjIdeal K v.asIdeal)
    (β : K) (hβ : β ∈ maximalRealSubfield K) :
    v.valuation K β = v'.valuation K β := by
  sorry -- follows from Helper A + complexConj_eq_self_iff

-- Helper C: valuation of product ideal (sign vector)
lemma valuation_J_eps (s : Fin m) (ε : Fin m → Bool) :
    (splitPrimeData.P s).valuation K (J_eps ε) = ε s - η s := by
  sorry -- from unique factorization + v_{𝔓_s}(𝔓_j) = if j=s then 1 else 0
```
