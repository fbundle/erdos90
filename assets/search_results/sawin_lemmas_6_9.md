# Sawin Paper — Lemmas 6–9 (pages 6–8): Relative Class Number and Fiber Construction

Source: `assets/arXiv-2605.20579v1.pdf`, pages 6–8

---

## Setup (page 4, notation)

- F = totally real number field, d = [F:ℚ]
- K = totally imaginary quadratic extension of F (CM field), c = complex conjugation
- N_{K/F} : fractional ideals of K → fractional ideals of F (relative norm)
- h^-(K) = h(K)/h(F) = **relative class number** (Sawin uses this, not h(K))
- Δ_K, Δ_F = discriminants; rd_{K/F} = (Δ_K/Δ_F)^{1/d} = relative root discriminant

---

## Lemma 6 (page 6): Size of G_K

Let G_K be the set of pairs (J, u) where J is a fractional ideal of K and u is a generator of N_{K/F}(J), up to equivalence (J, u) ~ ((α)J, αc(α)u) for α ∈ K×.

**Statement**: #G_K ≤ 2^{d+1} · h^-(K).

**Proof sketch**: Exact sequence 𝓞_K× → 𝓞_F× → G_K → Cl(K) → Cl(F). The cokernel of 𝓞_K× → 𝓞_F× is at most 2^d (norm map squared on units). The kernel of Cl(K) → Cl(F) has size h^-(K). Factor of 2 for unramified case.

**Lean relevance**: This is the group that plays the role of `cardG` in the Lean formalization. The Lean code uses `h(K)` (via `ClassGroup`) but Sawin gets a tighter bound via the relative class number.

---

## Lemma 7 (page 6–7): The Fiber Construction ← **KEY FOR ALL THREE SORRIES**

**Statement**: Let S_F be a set of prime ideals of 𝓞_F, and k : S_F → ℤ_{>0}. Assume each 𝔭 ∈ S_F splits in K. Then there exists a fractional ideal I of K and element α ∈ N_{K/F}(I) such that:
1. **#{β ∈ I : βc(β) = α} ≥ ∏_{𝔭∈S_F}(k(𝔭)+1) / (2^d · h^-(K))**
2. **#(N_{K/F}(I)/(α)) = ∏_{𝔭∈S_F} #(𝓞_F/𝔭)^{k(𝔭)** (= ∏ N(𝔭)^{k(𝔭)})

**Proof** (pages 6–7):

1. Consider the set L of ideals J ⊂ 𝓞_K with N_{K/F}(J) = ∏_{𝔭∈S_F} 𝔭^{k(𝔭)}. Since each 𝔭 splits as 𝔭 = 𝔭_1 · 𝔭_2 in K, each 𝔭 contributes k(𝔭)+1 choices. So #L = ∏_{𝔭}(k(𝔭)+1).

2. Map L → G_K by J ↦ (J·J_0^{-1}, 1) for a fixed J_0 ∈ L. Pigeonhole gives a fiber of size ≥ #L / #G_K ≥ ∏(k(𝔭)+1) / (2^{d+1}·h^-(K)). [The factor 2 is absorbed into the ≥ 2·#L/#G_K bound from the proof of Lemma 7.]

3. For J in this fiber, βJ_m = J·J_0^{-1} (equation (6), page 7). The β's satisfy βc(β) = 1 → u = α^{-1} in the normalization.

**The elements β in Lemma 7 correspond to u_ε = α_ε/c(α_ε) in the OpenAI paper.**

---

## Key Difference: Sawin vs. OpenAI Paper

| | OpenAI paper | Sawin paper |
|--|--|--|
| Group | Cl(K), size h(K) | G_K, size ≤ 2^{d+1}·h^-(K) |
| Fiber size | ≥ 2^m / h(K) | ≥ ∏(k(𝔭)+1) / (2^d·h^-(K)) |
| k values | k=1 for all 𝔭 (binary) | General k(𝔭) ≥ 1 |
| β elements | u_ε = α_ε/c(α_ε), βc(β)=1 | β ∈ I with βc(β) = α |

Sawin's Lemma 7 is strictly more general. Setting k(𝔭)=1 for all 𝔭 recovers the OpenAI paper's construction (up to the relative vs. absolute class number).

---

## Lemma 8 (page 7–8): Galois Case

When K is a Galois extension of ℚ (and F is Galois over ℚ), the bound on #{β} improves:
```
#{β} ≥ ∏_{p∈S_ℚ} (k(p)+1)^{d/(e_p·f_p)} / (2^d · h^-(K))
```
where e_p = ramification index, f_p = inertia degree of p in F.

**Not directly relevant to the Lean formalization** — the Lean code handles the special case where the q_b split completely (e_p = f_p = 1), giving the simpler bound.

---

## Lemma 9 (page 8): Relative Class Number Bound ← **KEY FOR `h_card_ratio`**

**Statement**: h^-(K) ≤ 8 rd_{K/F}^2 · (√rd_{K/F} · log(rd_{K/F}) · e/(4π))^d

**Proof**: Uses **Louboutin [11, Corollary 3]** — i.e., the paper `assets/louboutin_2000_class_number.pdf`.

The bound is:
```
h^-(K) ≤ 2Q_K w_K √(Δ_K/Δ_F) · (e·log(Δ_K/Δ_F) / (4π))^d
       = 2Q_K w_K rd_{K/F}^{d/2} · (e·log(rd_{K/F}) / (4π·1))^d · rd_{K/F}^d
```
- Q_K = Hasse unit index (1 or 2)
- w_K = number of roots of unity of K (≤ 2 rd_{K/F}^2 from cyclotomic bound)

**Applied to our fields**: rd_{K_j/F_j} ≤ 2 and rd_{F_j} = rd(F) = A_ℓ (constant in the tower).

So **log h^-(K_j) = O(f_j · log rd_{K_j})** = O(f_j · log(2·A_ℓ)) = O(f_j · ℓ log ℓ).

This gives a tighter bound than Minkowski: log h^-(K_j) = O(ℓ log ℓ · f_j) = (log H_ℓ) · f_j.

---

## Lean Relevance

### For `h_card_ratio`

The Lean code uses `cardG : ℕ` with bound `(cardG : ℝ) ≤ Real.exp (log_H * f)`. This comes from `h(K_j) ≤ H_ℓ^{f_j}` (OpenAI paper), equivalently `log h(K_j) ≤ f_j · log H_ℓ`.

From Sawin's Lemma 9, the same holds for h^-(K) (which is ≤ h(K)). Either bound suffices.

The Lean code `sorry`s this bound. To close it, need one of:
- `h_card_ratio_bound : (cardG : ℝ) ≤ Real.exp (log_H * ↑f)` as a sorried helper lemma (citing Louboutin + Sawin Lemma 9, or Minkowski + Neukirch I.5)
- Or provide the explicit `CMClassGroupData.hcardG` bound from the tower data

### For `hmk_unit_mem_Λ` and `hmk_unit_inj`

Sawin's Lemma 7 (equations (6)-(7), page 7) gives:
- βJ_m = J·J_0^{-1} as fractional ideals (equation (6))
- uβc(β) = 1 (equation (7)), where u is a generator of N_{K/F}(J_m)

The elements β in Lemma 7 satisfy βc(β) = u^{-1}. The integrality of β·(something) follows from the ideal equation (6) and the bounded denominators from the split primes.

The distinctness of β's follows from the fact that each J uniquely determines β via (6): if β₁J_m = J₁·J_0^{-1} and β₂J_m = J₂·J_0^{-1} and J₁ ≠ J₂, then β₁ ≠ β₂ (as ideals determine elements up to units in the fiber).

---

## Louboutin Reference (assets/louboutin_2000_class_number.pdf)

The paper already in assets is: **Louboutin 2000** — presumably "Explicit bounds for residues of Dedekind zeta functions" or similar, providing the explicit bound on h^-(K). Sawin cites it as [11, Corollary 3].

Full citation: Stéphane Louboutin. Explicit bounds for residues of Dedekind zeta functions, values of L-functions at s=1, and relative class numbers. *Journal of Number Theory*, 85(2):263–282, 2000.

The relevant bound (Corollary 3) is:
```
h^-(K) ≤ 2Q_K w_K √(|D_K|/|D_F|) · (e·log(|D_K|/|D_F|) / (4π·|D_K/D_F|^{1/2d}))^d
```
This gives an explicit upper bound for h^-(K) in terms of the relative discriminant Δ_K/Δ_F.
