# OpenAI Paper — Proposition 2.2 Full Construction (pages 6–7)

Source: `assets/unit-distance-proof.pdf`, pages 6–9

---

## Proposition 2.2 (page 6)

**Statement**: Let L, K, t, q₁,...,qₜ, Q be an admissible datum (Definition 2.1). Suppose h(K) ≤ H^f for some real H > 0. Then there is a set U ⊂ Q^{-2}𝓞_K such that every u ∈ U satisfies N_{K/L}(u) = 1, where for K = L(i), N_{K/L}(u) = u·c(u). Every u ∈ U also satisfies |σ(u)| = 1 for every complex embedding σ : K ↪ ℂ. Moreover, |U| ≥ exp{(t log 2 − log H)f}.

---

## The Construction (proof, page 7)

For each binary vector ε = (ε_s) ∈ {0,1}^m, define the ideal:
```
𝔄_ε = ∏_{ε_s=1} 𝔓_s  ·  ∏_{ε_s=0} c𝔓_s
```

**Size**: These 2^m ideals occupy only h(K) ideal classes (class group has order h(K)). By pigeonhole, some fiber of ε ↦ [𝔄_ε] ∈ Cl(K) has size ≥ 2^m / h(K).

**Fix η in such a fiber**. For every ε in the same fiber:
- 𝔄_ε · 𝔄_η^{-1} is principal
- Choose α_ε ∈ K× with (α_ε) = 𝔄_ε · 𝔄_η^{-1}
- Set u_ε = α_ε / c(α_ε)

**Norm-1 property**: u_ε · c(u_ε) = (α_ε/c(α_ε)) · (c(α_ε)/α_ε) = 1. Equivalently, N_{K/L}(u_ε) = 1. Since L is totally real, c becomes ordinary complex conjugation under every complex embedding σ of K. Therefore |σ(u_ε)| = |σ(α_ε)/σ̄(α_ε)| = 1.

---

## Key Valuation Formula (equation (4), page 7)

The principal ideal of u_ε is:
```
(u_ε) = (𝔄_ε · 𝔄_η^{-1}) / c(𝔄_ε · 𝔄_η^{-1})
```

At the chosen split prime pairs, **equation (4)**:
```
v_{𝔓_s}(u_ε)   =  2(ε_s − η_s)
v_{c𝔓_s}(u_ε)  = −2(ε_s − η_s)
```

**Integrality argument** (page 7):  
"The displayed ideal identity and (4) show that all poles of u_ε have order at most 2 and lie above the q_b's. Since Q𝓞_K has valuation 1 at each such prime, Q²u_ε ∈ 𝓞_K. So u_ε ∈ Q^{-2}𝓞_K."

**Injectivity / distinctness** (page 7):  
"By (4), distinct ε's give distinct valuation vectors, hence distinct elements u_ε."

This gives |U| ≥ 2^m / h(K) ≥ exp{(t log 2 − log H)f} (using m = tf and h(K) ≤ H^f).

---

## Mapping to the Lean Formalization

| Paper | Lean (`exists_cm_class_group_data`) |
|-------|--------------------------------------|
| ε ∈ {0,1}^m | `ε : E = Fin m → Bool` |
| 𝔄_ε | `J ε` (product of 𝔓_s or c𝔓_s per ε_s) |
| η (fixed fiber representative) | implicit in `h_exists_alpha ε₁ ε₂ hφ_eq` |
| α_ε with (α_ε) = 𝔄_ε · 𝔄_η^{-1} | `α := Classical.choose (h_exists_alpha ε₁ ε₂ hφ_eq)` |
| u_ε = α_ε/c(α_ε) | `mk_unit ε₁ ε₂ = cmData.φ (mixedEmbedding K (α / complexConj K α))` |
| U ⊂ Q^{-2}𝓞_K = Λ | `mk_unit ε₁ ε₂ ∈ Λ` (sorry `hmk_unit_mem_Λ`) |
| distinct valuation vectors → distinct u_ε | `mk_unit ε₁ ε₂ = mk_unit ε₁ ε₃ → ε₂ = ε₃` (sorry `hmk_unit_inj`) |

---

## What Each Sorry Needs

### `hmk_unit_mem_Λ` (integrality, line 573)

**Mathematical content**: v_{𝔓_s}(α/c(α)) = 2(ε_s − η_s) ∈ {-2, 0, 2} for each split prime 𝔓_s. All other primes give valuation 0. Since Q𝓞_K has valuation 1 at 𝔓_s, v_{𝔓_s}(Q²) = 2. Therefore v_{𝔓_s}(Q²·(α/c(α))) = 2 + 2(ε_s − η_s) ≥ 0. Hence Q²·α/c(α) ∈ 𝓞_K, so α/c(α) ∈ Q^{-2}𝓞_K = Λ.

**Lean gap**: Need to compute v_{𝔓_s}(α/c(α)) from the ideal equation (α) = 𝔄_ε · 𝔄_η^{-1}. Requires:
1. `IsDedekindDomain.HeightOneSpectrum.valuation` applied to α at 𝔓_s
2. The valuation of a product ideal equals sum of valuations
3. v_{𝔓_s}(𝔄_ε) = ε_s (since 𝔄_ε = 𝔓_s^{ε_s} · (c𝔓_s)^{1-ε_s} at position s)
4. v_{𝔓_s}(c(α)) = v_{c𝔓_s}(α) (conjugation swaps valuations at conjugate primes)

### `hmk_unit_inj` (injectivity, line 656)

**Mathematical content**: If mk_unit(η, ε₂) = mk_unit(η, ε₃), then u_{ε₂} = u_{ε₃} (by Minkowski injectivity). Then for each s: 2(ε₂_s − η_s) = v_{𝔓_s}(u_{ε₂}) = v_{𝔓_s}(u_{ε₃}) = 2(ε₃_s − η_s). Hence ε₂_s = ε₃_s for all s.

**Lean gap**: Same requirements as `hmk_unit_mem_Λ` plus reading off ε from valuations.

**Note**: The Lean code currently pursues a different path (Lemma A + Lemma B: α₂/α₃ ∈ K⁺ → valuation parity). The paper's argument is more direct: compare valuation vectors of u_{ε₂} and u_{ε₃} directly.

### `h_card_ratio` (class number bound, line 494)

**Mathematical content**: h(K_j) ≤ H_ℓ^{f_j} where log H_ℓ = O(ℓ log ℓ). This uses:
- Proposition 3.7 (page 12): h(K) ≤ max{2, rd(K)}^{C_class·[K:ℚ]} (Minkowski bound + counting ideals)
- rd(K_j) ≤ 2·rd(F) ≤ 2·A_ℓ where log A_ℓ = O(ℓ log ℓ)
- So log h(K_j) ≤ C_class·2f·log(2A_ℓ) = O(ℓ log ℓ)·f = (log H_ℓ)·f

**References**: [Neu99, Chapter I, Section 5] (Minkowski bound), [Lan94, Chapter V] (class number bounds)

---

## Proposition 3.7 (Class Number Bound, page 12)

**Statement**: There is an absolute constant C_class > 0 such that every number field K satisfies:
```
h(K) ≤ max{2, rd(K)}^{C_class · [K:ℚ]}
```
where rd(K) = |D_K|^{1/[K:ℚ]} is the root discriminant.

This is the "class-number consequence of Minkowski's ideal-class bound" — Minkowski shows every ideal class has a representative of norm ≤ (C√A)^n, and counting ideals of bounded norm via the n-fold divisor function gives the bound.

**References**:
- [Neu99] = Neukirch, Algebraic Number Theory, Chapter I, Section 5
- [Lan94] = Lang, Algebraic Number Theory, Chapter V
- Also: Proposition A.13 in the paper's appendix
