# Derivation of the Key Valuation Formula v_{𝔓_s}(u_ε) = 2(ε_s − η_s)

Source: OpenAI paper equation (4) + Mathlib `AdicValuation.lean` API

---

## Setup

Given:
- CM field K, totally real subfield L = F (of degree f = [L:ℚ])
- Split primes q_b ≡ 1 (mod 4), b = 1,...,t; Q = ∏ q_b
- For each q_b, f conjugate prime pairs {(𝔓_s, c𝔓_s) : s ∈ fiber over q_b}; total m = tf pairs
- ε = (ε_s) ∈ {0,1}^m = Fin m → Bool (sign vector)
- 𝔄_ε = ∏_{ε_s=1} 𝔓_s · ∏_{ε_s=0} c𝔓_s (the signed product ideal)
- η ∈ {0,1}^m fixed (the fiber representative)
- α_ε ∈ K× with principal ideal (α_ε) = 𝔄_ε · 𝔄_η^{-1}
- u_ε = α_ε / c(α_ε)

---

## Step 1: Valuation of 𝔄_ε at 𝔓_s

Since 𝔓_s and c𝔓_s are **distinct** prime ideals (q_s splits completely), the unique factorization gives:
```
v_{𝔓_s}(𝔄_ε) = ε_s        (exponent of 𝔓_s in 𝔄_ε)
v_{c𝔓_s}(𝔄_ε) = 1 - ε_s   (exponent of c𝔓_s in 𝔄_ε)
```

**Mathlib API**: `intValuationDef_if_neg`:
```lean
v.intValuationDef r = exp (-(Associates.mk v.asIdeal).count
    (Associates.mk (Ideal.span {r})).factors : ℤ)
```
The count is the multiplicity of v.asIdeal in the factorization of (r).

---

## Step 2: Valuation of (α_ε) at 𝔓_s

From (α_ε) = 𝔄_ε · 𝔄_η^{-1} (the ideal equation from `ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring`):

```
v_{𝔓_s}((α_ε)) = v_{𝔓_s}(𝔄_ε) - v_{𝔓_s}(𝔄_η)
               = ε_s - η_s
```

Similarly: `v_{c𝔓_s}((α_ε)) = (1-ε_s) - (1-η_s) = η_s - ε_s = -(ε_s - η_s)`

**Mathlib API**: `intValuation.map_mul'` (line 111):
```lean
theorem intValuation.map_mul' (x y : R) :
    v.intValuationDef (x * y) = v.intValuationDef x * v.intValuationDef y
```
Combined with `valuation_of_mk'` for fractions.

---

## Step 3: Valuation-Conjugation Swap

The **missing** lemma: v_{𝔓_s}(c(α_ε)) = v_{c𝔓_s}(α_ε).

**Mathematical justification**: The complex conjugation c : K → K is a field automorphism with c(𝔓_s) = c𝔓_s (by definition of conjIdeal). For any automorphism σ of K:
```
v_{σ𝔭}(σα) = v_{𝔭}(α)    for all α ∈ K× and prime 𝔭
```
Applied with σ = c, α = α_ε, 𝔭 = 𝔓_s:
```
v_{c𝔓_s}(c(α_ε)) = v_{𝔓_s}(α_ε)
```
But we want v_{𝔓_s}(c(α_ε)):
```
v_{𝔓_s}(c(α_ε)) = v_{c^{-1}𝔓_s}(α_ε) = v_{c𝔓_s}(α_ε)
```
(using c^{-1} = c since c² = id).

So: `v_{𝔓_s}(c(α_ε)) = v_{c𝔓_s}(α_ε) = -(ε_s - η_s)`

**NOT in Mathlib**: `IsDedekindDomain.HeightOneSpectrum` has no automorphism-equivariance lemma. This is the core gap.

**Workaround**: Add a sorry'd helper lemma in `CMField/Basic.lean`:
```lean
/-- Complex conjugation swaps valuations at conjugate prime pairs.
    [Neukirch, Algebraic Number Theory, Proposition I.8.5] -/
lemma conjIdeal_valuation_swap (𝔓 : HeightOneSpectrum (𝓞 K))
    (α : K) (hα : α ≠ 0) :
    (HeightOneSpectrum.mk (conjIdeal K 𝔓.asIdeal) ...).valuation K (IsCMField.complexConj K α) =
    𝔓.valuation K α := by
  sorry
```

---

## Step 4: Valuation of u_ε

```
v_{𝔓_s}(u_ε) = v_{𝔓_s}(α_ε / c(α_ε))
             = v_{𝔓_s}(α_ε) - v_{𝔓_s}(c(α_ε))
             = (ε_s - η_s) - (-(ε_s - η_s))
             = 2(ε_s - η_s)
```

This is equation (4) of the OpenAI paper.

**Corollary (integrality)**: v_{𝔓_s}(u_ε) ∈ {-2, 0, 2}. Since v_{𝔓_s}(Q) = 1 (Q = q_{b(s)}·𝓞_K has valuation 1 at 𝔓_s), v_{𝔓_s}(Q²·u_ε) = 2 + v_{𝔓_s}(u_ε) ≥ 0. So Q²·u_ε ∈ 𝓞_K.

**Corollary (distinctness)**: If ε ≠ ε', ∃ s with ε_s ≠ ε'_s, so 2(ε_s-η_s) ≠ 2(ε'_s-η_s), so v_{𝔓_s}(u_ε) ≠ v_{𝔓_s}(u_{ε'}), so u_ε ≠ u_{ε'}.

---

## Reference for the Automorphism-Equivariance Lemma

**Neukirch, Algebraic Number Theory** (1999), Chapter I, §8:

Proposition I.8.5 (paraphrased): Let L/K be a Galois extension of number fields, σ ∈ Gal(L/K), and 𝔓 a prime ideal of 𝓞_L lying over 𝔭 ⊂ 𝓞_K. Then for x ∈ L×:
```
v_{σ𝔓}(σx) = v_{𝔓}(x)
```
In particular, v_{σ𝔓}(x) = v_{𝔓}(σ^{-1}x) for any x ∈ L×.

**Applied**: With L = K, K = ℚ (or K = F), σ = c (complex conjugation), 𝔓 = 𝔓_s, x = α_ε.

---

## Lean Proof Sketch for `hmk_unit_mem_Λ`

```lean
-- Assuming the three helper lemmas are available:
have h_val_u : v_{𝔓_s} u_ε = exp (2 * (ε_s - η_s) : ℤ) := by
  -- (1) v_{𝔓_s}(α_ε) = ε_s - η_s from ideal factorization
  -- (2) v_{𝔓_s}(c(α_ε)) = -(ε_s - η_s) from conjIdeal_valuation_swap
  -- (3) v_{𝔓_s}(u_ε) = v_{𝔓_s}(α_ε) / v_{𝔓_s}(c(α_ε)) [multiplicativity of valuation]
  sorry

have h_Q2u_int : Q^2 * u_ε ∈ 𝓞K := by
  -- v_{𝔓_s}(Q^2 * u_ε) = 2 + 2*(ε_s - η_s) ≥ 0 for all s
  -- v_𝔭(Q^2 * u_ε) = 0 for all 𝔭 not above any q_b
  -- Hence Q^2 * u_ε ∈ 𝓞K by the product formula
  sorry
```

---

## Lean Proof Sketch for `hmk_unit_inj`

```lean
-- Given mk_unit ε₁ ε₂ = mk_unit ε₁ ε₃ (i.e., u_{ε₂} = u_{ε₃})
-- For each s: v_{𝔓_s}(u_{ε₂}) = v_{𝔓_s}(u_{ε₃})
-- So 2(ε₂_s - η_s) = 2(ε₃_s - η_s)
-- So ε₂_s = ε₃_s for all s
-- So ε₂ = ε₃
```

The Lean code currently takes a detour through α₂/α₃ ∈ K⁺. The direct paper argument above is simpler and should be preferred.
