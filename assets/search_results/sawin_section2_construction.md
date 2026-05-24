# Sawin 2026 — Section 2 Construction (Sign-Vector / Class-Group)

Source: https://arxiv.org/html/2605.20579v1  
Paper: "An explicit lower bound for the unit distance problem" — Will Sawin, May 2026

---

## Correction to Current `CMClassGroupData` Docstring

The current docstring describes E = {±1}^m and φ : E → G, but the actual
Sawin construction is more nuanced. The set L (playing the role of E) is
defined as ideals with a fixed relative norm, not as sign vectors.

---

## The Set L (plays role of E)

Given:
- CM field K = F(√-1), where F is totally real (from the GS tower)
- S_F = finite set of prime ideals 𝔭 ⊂ O_F, each split in K/F
  (so each 𝔭 = 𝔓·c(𝔓) in O_K)
- k : S_F → ℤ₊ an exponent function

Define: L = { ideals J ⊂ O_K : N_{K/F}(J) = ∏_{𝔭 ∈ S_F} 𝔭^{k(𝔭)} }

For each split prime 𝔭 = 𝔓·c(𝔓), there are exactly k(𝔭)+1 choices of
exponent j ∈ {0, …, k(𝔭)} giving 𝔓^j · c(𝔓)^{k(𝔭)-j}.

**Key size bound**: |L| = ∏_{𝔭 ∈ S_F} (k(𝔭) + 1)

Setting k(𝔭) = 1 for all 𝔭 gives |L| = 2^|S_F| — the sign-vector
interpretation {±1}^m arises by encoding j=0 as +1 and j=1 as -1.

---

## The Group G_K (plays role of G in pigeonhole)

G_K = { pairs (J, u) : J fractional ideal of K, u ∈ F×, u = N_{K/F}(J) }
      modulo equivalence: (J, u) ~ ((α)J, αc(α)u) for α ∈ K×.

**Size bound**: #G_K ≤ 2^{[K:ℚ]+1} · h⁻(K)

where h⁻(K) = h(K)/h(F) is the relative class number.

---

## Lemma 7 (Pigeonhole — plays role of `exists_fiber_ge_div`)

Map φ : L → G_K by φ(J) = class of (J, N_{K/F}(J)).

By pigeonhole, ∃ fiber with |fiber| ≥ |L| / #G_K.

**Key**: Two ideals J₁, J₂ in the same fiber satisfy
N_{K/F}(J₁·J₂⁻¹) = 1, so J₁·J₂⁻¹ is a relative ideal.
By class-group arguments, J₁·J₂⁻¹ is PRINCIPAL = (α) for some α ∈ K×.

---

## Norm-1 Property (plays role of `hmk_unit_norm`)

For J₁, J₂ in the same fiber: J₁·J₂⁻¹ = (α), so

  N_{K/F}(J₁·J₂⁻¹) = (α · c(α)) = N_{K/F}(J₁)/N_{K/F}(J₂) = 1

This means α · c(α) = unit ∈ O_F×. In the standard Sawin construction
with k(𝔭) = 1, this gives α · c(α) ∈ {±1}. Then α/c(α) has norm 1 at
every complex embedding:

  |φ(α/c(α))|² = φ(α) · conj(φ(α)) = φ(α) · φ(c(α)) = φ(α · c(α)) = 1

This uses `IsCMField.complexEmbedding_complexConj` (available in Mathlib).

---

## Injectivity (plays role of `hmk_unit_inj`)

**NOT a valuation parity argument.** The actual argument is:

1. Suppose Φ(α₁₂/c(α₁₂)) = Φ(α₁₃/c(α₁₃)) (same Minkowski embedding).
2. Since Φ : K → ℂ^f is injective: α₁₂/c(α₁₂) = α₁₃/c(α₁₃).
3. Let β = α₁₂/α₁₃. Then β/c(β) = 1, so β = c(β).
4. By `IsCMField.complexConj_eq_self_iff`: β ∈ K⁺ (the totally real subfield).
5. So (α₁₂) = β·(α₁₃) with β ∈ K⁺×, meaning J₁₂ = (β)·J₁₃.
6. But J₁₂ and J₁₃ are distinct elements of L (different exponent vectors
   at split primes). The ideal (β) ⊂ O_K with β ∈ K⁺× has relative norm
   N_{K/F}((β)) = (β²), which can only equal 1 if β = ±1 (unit in O_{K⁺}).
7. Since |β| = 1 at every real place (β ∈ K⁺ = totally real field and β is
   a unit), the only possibilities are β = ±1, but then J₁₂ = ±J₁₃, which
   forces ε₂ = ε₃ (same exponent vector mod sign) — giving the same
   element of L.

**Lean implementation note**: The key steps are:
- `IsCMField.complexConj_eq_self_iff` (available) for step 4
- Ideal equality J₁₂ = β·J₁₃ → same element of L (requires ideal factorization at split primes, not in Mathlib)

---

## The CM Field K (root cause of all three sorries)

K = F(√-1) where F is the GS tower field.

In Mathlib: `IsCyclotomicExtension.Rat.isCMField` gives CM for cyclotomic
fields, but the GS tower field F is NOT cyclotomic — it's built by
Golod-Shafarevich, which has no Lean formalization.

**Missing piece**: A Lean term `K : Type*` with `[Field K] [NumberField K]
[IsCMField K] [IsGalois ℚ K] [IsTotallyComplex K]` and
`Module.finrank ℚ K = 2 * f` for arbitrary f, coming from a pro-3 tower.

---

## Relevant Load-Bearing Lemmas in Sawin (2605.20579)

| Lemma | Content | Lean status |
|---|---|---|
| Lemma 4 | ‖α/c(α)‖ = 1 at each complex embedding | **PROVED** in §4 |
| Lemma 7 | Pigeonhole on L → G_K | **PROVED** as `exists_fiber_ge_div` |
| Lemma 12 | CM field K = F(√-1) exists from GS tower | **SORRY** (`gs_tower_levels`) |
| Lemma 6 | Relative class number bound: log h⁻(K) ≤ [K:ℚ]·log(rd(K)) | **SORRY** (implied by `log_H` bound) |
| Sec 2.1 | Construction of α from J₁·J₂⁻¹ being principal | **SORRY** (`hmk_unit_norm`) |
| Sec 2.2 | Injectivity ε₂ ↦ α₁₂/c(α₁₂) via ideal recovery | **SORRY** (`hmk_unit_inj`) |
