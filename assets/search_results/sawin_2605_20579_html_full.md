# Source: https://arxiv.org/html/2605.20579

# An Explicit Lower Bound for the Unit Distance Problem

**Author:** Will Sawin
**arXiv:** 2605.20579v1 [math.CO] May 2026

---

## Abstract

The paper proves that sets of n points in the plane can contain more than n^1.014 pairs at unit distance, significantly improving previous bounds and disproving Erdős's conjecture. The method uses algebraic number fields of large degree and small discriminant with primes of small norm via a Golod-Shafarevich criterion argument.

---

## Main Theorem

**Theorem 1:** For arbitrarily large n, there exists a set of points U ⊂ ℝ² with #U = n and at least n^1.014114/C pairs separated by distance exactly 1, where C is an absolute constant.

The upper bound is O(n^4/3) (Spencer-Szemerédi-Trotter). Previous lower bounds had the form n^(1+c/log log n) per Erdős.

---

## Key Lemmas and Propositions (Complete Statements and Proofs)

### Lemma 2

**Statement:** Given a lattice Λ in ℝ^(2d) with norm ‖·‖, an injective homomorphism π: Λ → ℝ², and M vectors with ‖v‖ ≤ 1 and |π(v)| = 1, then for R > 1 there exists U ⊆ ℝ² such that #U ≤ (2R/ρ+1)^(2d) and the ratio of unit-distance pairs to total points is at least (1-1/R)^(2d) M.

**Proof:** "We let B(r,w) be the ball of radius r around w. Choose U = π(B(R,w) ∩ Λ) for suitable w. The balls of radius ρ/2 around points in B(R,w) ∩ Λ are disjoint and contained in B(R+ρ/2,w), giving #U ≤ (2R/ρ+1)^(2d)."

"For any v₁ ∈ B(R-1,w) ∩ Λ, if v ∈ Λ with ‖v‖ ≤ 1 and |π(v)| = 1, then v₁+v ∈ B(R,w) ∩ Λ. The expected value of #(B(R-1,w) ∩ Λ) - (1-1/R)^(2d) #(B(R,w) ∩ Λ) over w equals zero, so we can choose w satisfying #(B(R-1,w) ∩ Λ) ≥ (1-1/R)^(2d) #(B(R,w) ∩ Λ). Combining these bounds yields the conclusion."

---

### Lemma 3

**Statement:** For a fractional ideal I of K, β ∈ I, and α ∈ N_(K/F)(I), the ratio #(I/(β)) / #(N_(K/F)(I)/(α)) equals ∏_(v ∈ Σ_(F,∞)) |β|_v² / |α|_v.

**Proof:** "By the Chinese remainder theorem and product formula, #(I/(β)) = ∏_(v ∈ V_K \ Σ_(K,∞)) |I|_v/|β|_v · ∏_(v ∈ Σ_(K,∞)) |β|_v² = ∏_(v ∈ V_K \ Σ_(K,∞)) |I|_v · ∏_(v ∈ Σ_(F,∞)) |β|_v²."

"Similarly, #(N_(K/F)(I)/(α)) = ∏_(v ∈ V_F \ Σ_(F,∞)) |N_(K/F)(I)|_v · ∏_(v ∈ Σ_(F,∞)) |α|_v. Since ∏_(v ∈ V_F \ Σ_(F,∞)) |N_(K/F)(I)|_v = ∏_(v ∈ V_K \ Σ_(K,∞)) |I|_v by matching places, the ratio equals ∏_(v ∈ Σ_(F,∞)) |β|_v² / |α|_v."

---

### Lemma 4

**Statement:** For a fractional ideal I of K and α ∈ N_(K/F)(I), the ideal I as a lattice has minimum nonzero norm (#(N_(K/F)(I)/(α)))^(-1/2d), and elements β with β c(β) = α satisfy ‖β‖ = 1 and |π(β)| = 1.

**Proof:** "For β ∈ I with βc(β) = α, we have |β|_v = √(|βc(β)|_v) = √(|α|_v) for all v ∈ Σ_(F,∞), so ‖β‖ = sup_(v ∈ Σ_(F,∞))(|β|_v / √(|α|_v)) = 1 and |π(β)| = |β|_v / √(|α|_v) = 1."

"For nonzero β ∈ I, by Lemma 3: ∏_(v ∈ Σ_(F,∞)) |β|_v / √(|α|_v) = √(#(I/(β)) / #(N_(K/F)(I)/(α))) ≥ 1/√(#(N_(K/F)(I)/(α))). Since #Σ_(F,∞) = d, we obtain sup_(v ∈ Σ_(F,∞)) |β|_v / √(|α|_v) ≥ (#(N_(K/F)(I)/(α)))^(-1/2d)."

---

### Lemma 5

**Statement:** For a fractional ideal I, α ∈ N_(K/F)(I), and M elements β ∈ I with βc(β) = α, there exists U ⊆ ℝ² with #U ≤ (2R(#(N_(K/F)(I)/(α)))^(1/2d)+1)^(2d) and unit-distance count ≥ (1-1/R)^(2d) M.

**Proof:** "This follows directly from combining Lemma 2 and Lemma 4 by setting ρ = (#(N_(K/F)(I)/(α)))^(-1/2d) and M equal to the count of β ∈ I with βc(β) = α."

---

### Lemma 6

**Statement:** The set G_K of pairs (J, u) modulo equivalence satisfies #G_K ≤ 2^(d+1) h^-(K).

**Proof:** "G_K forms a group under (J₁,u₁)(J₂,u₂) = (J₁J₂, u₁u₂). The exact sequence 𝒪_K^× → 𝒪_F^× → G_K → Cl(K) → Cl(F) gives #G_K = #coker(𝒪_K^× → 𝒪_F^×) · h(K)/h(F) · #coker(Cl(K) → Cl(F))."

"Since the norm map on 𝒪_F^× is squaring, #coker(𝒪_K^× → 𝒪_F^×) ≤ #(𝒪_F^× / (𝒪_F^×)²) ≤ 2^d by Dirichlet's unit theorem. By class field theory, #coker(Cl(K) → Cl(F)) ≤ 2. Therefore #G_K ≤ 2^d · 2 · h(K)/h(F) = 2^(d+1) h^-(K)."

---

### Lemma 7

**Statement:** For split primes in S_F with function k, there exist a fractional ideal I and α ∈ N_(K/F)(I) with M ≥ ∏_(𝔭 ∈ S_F)(k(𝔭)+1) / (2^d h^-(K)) elements β ∈ I satisfying βc(β) = α, and #(N_(K/F)(I)/(α)) = ∏_(𝔭 ∈ S_F) #(𝒪_F/𝔭)^(k(𝔭)).

**Proof:** "Let L be the set of ideals J with N_(K/F)(J) = ∏_(𝔭 ∈ S_F) 𝔭^(k(𝔭)). Since each 𝔭 splits into two primes 𝔭₁, 𝔭₂, we can form ideals 𝔭₁^j 𝔭₂^(k(𝔭)-j) for j ∈ {0,...,k(𝔭)}, giving #L = ∏_(𝔭 ∈ S_F)(k(𝔭)+1)."

"Fix J₀ ∈ L. The map J ↦ (JJ₀^(-1), 1) sends L to G_K with each fiber having size ≥ #L/#G_K. Thus there exist J_m and u generating N_(K/F)(J_m) such that for ≥ #L/#G_K ideals J ∈ L, there exists β ∈ K with βJ_m = JJ₀^(-1) and uβc(β) = 1."

"Setting I = J₀^(-1) J_m^(-1) and α = u^(-1), we have β ∈ I satisfying βc(β) = α for ≥ #L/#G_K choices, and since ±β both work, we get ≥ 2#L/#G_K. By Lemma 6, this is ≥ ∏_(𝔭 ∈ S_F)(k(𝔭)+1) / (2^d h^-(K)). Also, #(N_(K/F)(I)/(α)) = #(𝒪_F / ∏_(𝔭 ∈ S_F) 𝔭^(k(𝔭))) = ∏_(𝔭 ∈ S_F) #(𝒪_F/𝔭)^(k(𝔭))."

---

### Lemma 8

**Statement:** For Galois K/F and primes p ∈ S_ℚ with ramification index e_p and inertia degree f_p, there exist I and α with M ≥ ∏_(p ∈ S_ℚ)(k(p)+1)^(d/(e_p f_p)) / (2^d h^-(K)) and #(N_(K/F)(I)/(α)) = ∏_(p ∈ S_ℚ) p^(k(p)d/e_p).

**Proof:** "In a Galois extension K/ℚ with F Galois over ℚ, each prime p ∈ S_ℚ lying over primes in F has d/(e_p f_p) distinct primes lying above it in F, each with residue field of size p^(f_p). Apply Lemma 7 with S_F as the set of primes lying over primes in S_ℚ, taking k(𝔭) = k(p) for 𝔭 | p. The factor (k(𝔭)+1) becomes (k(p)+1)^(d/(e_p f_p)) and the exponent in the norm becomes p^(k(p)d/e_p)."

---

### Lemma 9

**Statement:** The relative class number satisfies h^-(K) ≤ 8 rd_(K/F)² (√(rd_(K/F)) log(rd_(K/F)) e/(4π))^d.

**Proof:** "Louboutin's bound states h^-(K) ≤ 2 Q_K w_K √(Δ_K/Δ_F) (e/(4πd) · log(Δ_K/Δ_F))^d where Q_K ∈ {1,2} and w_K is the number of roots of unity."

"Since w_K ≤ 2 rd_(K/F)² and rd_(K/F)² = Δ_K/Δ_F, we get h^-(K) ≤ 2 · 2 · rd_(K/F)² · rd_(K/F)^(d/2) · (e · log(rd_(K/F)) / (4π))^d = 8 rd_(K/F)² (√(rd_(K/F)) · log(rd_(K/F)) · e/(4π))^d."

---

### Lemma 11

**Statement:** For the Golod-Shafarevich criterion applied to 2-class field towers:
(1) ℚ({√q | q ∈ T})/ℚ is an everywhere unramified Galois extension with Galois group (ℤ/2ℤ)^(#T-1);
(2) d(G) ≥ #T - 1;
(3) r(G) ≤ d(G) + #S_ℚ + #{p ∈ S_ℚ | p splits in ℚ} + 2;
(4) G is infinite if condition (9) holds.

**Proof:**

**(1)** "The extension ℚ({√q | q ∈ T})/ℚ is Galois with Galois group (ℤ/2ℤ)^(#T-1). For unramifiedness: ℚ(√q)/ℚ is unramified away from odd primes dividing q and ∏_(q' ∈ T\{q}) q'. Since the number of elements in T congruent to 3 mod 4 is odd, no odd prime divides both, and 2 ramifies in at most one. Thus no place ramifies in both extensions."

**(2)** "The Galois group (ℤ/2ℤ)^(#T-1) of ℚ({√q | q ∈ T})/ℚ is a quotient of G, so d(G) ≥ #T-1."

**(3)** "G is the quotient of the maximal 2-group Galois group of unramified extensions of Q by the normal closure of Frobenius elements at split primes. The number of relations added is ≤ d(G) + #S_ℚ + #{p ∈ S_ℚ | p splits in Q} + 2 by quotient analysis."

**(4)** "By the Golod-Shafarevich theorem (Gaschütz-Vinberg), G is infinite if r(G) ≤ d(G)²/4. Using d(G) ≥ #T-1 and the bound on r(G) from (3), infiniteness holds when #T + #S_ℚ + #{p ∈ S_ℚ | p splits in Q} + 1 ≤ (#T-1)²/4."

---

### Lemma 12

**Statement:** Under conditions of Lemma 11, there exist Galois extensions F of ℚ of arbitrarily large degree, totally real, such that K = F(√(-1)) has rd_(K/F) = √(4 ∏_(q ∈ T) q), with all primes in S_ℚ splitting in K/F.

**Proof:** "Since G is infinite by Lemma 11(4), the maximal pro-2 quotient has arbitrarily large finite quotients surjecting onto Gal(ℚ({√q | q ∈ T})/ℚ). Each quotient corresponds to a Galois extension F' of ℚ that is unramified and totally real with inertia degrees ≤ 2 at relevant primes."

"To make F Galois over ℚ, take F = F' F* where F* is the pullback along the nontrivial automorphism of ℚ. Properties are preserved under composition."

"Since F is unramified over Q and K = F(√(-1)) is unramified over F at all finite places (including 2, since -∏_(q ∈ T) q ≡ 1 mod 4), we have Δ_K/Δ_F = Δ_F (ratio of 1). Thus rd_(K/F) = √(Δ_Q^([F:ℚ]/2)) = √(4 ∏_(q ∈ T) q). For primes p ∈ S_ℚ, all split in K/F by inertia degree analysis."

---

### Proposition 10

**Statement:** For fields satisfying stated conditions with arbitrarily large degree and rd_(K/F) = λ, sets U exist for any R > 1 with δ as defined in equation (8), yielding #U ≤ (2R ∏_(p ∈ S_ℚ) p^(k(p)/(2e(p)))+1)^(2d) and unit-distance count ≥ (#U)^(1+δ) / (8λ²).

**Proof:** "Apply Lemma 8 to get ideal I and α. By Lemma 5, #U ≤ (2R(#(N_(K/F)(I)/(α)))^(1/2d)+1)^(2d) ≤ (2R ∏_(p ∈ S_ℚ) p^(k(p)/(2e(p)))+1)^(2d) and unit-distance density ≥ (1-1/R)^(2d) · ∏_(p ∈ S_ℚ)(k(p)+1)^(d/(e(p)f(p))) / (2^d h^-(K))."

"Apply Lemma 9 to bound h^-(K) ≤ 8λ²(√λ · log(λ) · e/(4π))^d. Taking logarithms and dividing, the exponent of #U in the unit-distance count is 1+δ where δ is equation (8). Since δ > 0, both #U and unit-distance count are arbitrarily large."

---

### Proposition 15

**Statement:** For any field configuration, the exponent from equation (12) is at most 1 + 1/4.116 ≈ 1.243.

**Proof:** "Fixing c > 0, analyze the numerator-denominator difference in equation (12). The term log(1-1/R) - log(R) is maximized at R = c+1, giving c · log(c/(c+1)) - log(c+1). The class number term contributes ≥ 0. The prime sum contributes ≤ d · ∑_p max_k(c · log(k+1) - k · log p)/2."

"Setting c = 4.116 and computing with maximal k values (k=5 for p=2, k=3 for p=3, k=2 for p=5, k=1 for p=7,11,13,17, k=0 else), the total is negative. Therefore equation (12) ≤ 1 + 1/4.116 ≈ 1.243."

---

## Key Definitions

- **CM field K/F:** K is a totally imaginary quadratic extension of totally real F.
- **Relative class number:** h^-(K) = h(K)/h(F).
- **Relative root discriminant:** rd_(K/F) = (Δ_K/Δ_F)^(1/d).
- **N_(K/F):** Norm map from ideals of K to ideals of F.
- **G_K:** The set of pairs (J, u) where J is a fractional ideal of K and u ∈ N_(K/F)(J), modulo equivalence.
- **c:** Complex conjugation on K (the unique nontrivial automorphism of K/F for CM field K).

---

## Explicit Parameters

The proof achieves δ ≈ 0.014114 by selecting:
- T = {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43}
- S_ℚ containing 22 strategic primes
- Optimized values k(p) for each prime using parameter t = 35.5

## Improvements Over Prior Work

The approach differs from OpenAI's concurrent work by:
- Using ideals instead of just rings of integers
- Applying relative class numbers over absolute class numbers
- Avoiding restrictions to split primes
- Using power functions k(𝔭) for prime ideals
- Employing unramified extensions rather than ramified ones

Remark 13 explains how to extend results to multiple values of n simultaneously.

---

## References (Key Citations)

- Erdős (1946, 1982, 1994): Original distance set problems and conjectures
- Spencer-Szemerédi-Trotter (1984): Upper bound O(n^4/3)
- OpenAI (2026): Recent breakthrough with inexplicit exponent
- Louboutin (2000): Class number bounds via L-functions
- Golod-Shafarevich (1964): Infinite class field towers
- Neukirch-Schmidt-Wingberg (2008): Cohomology of number fields
- Hajir-Maire-Ramakrishna: Controlled root discriminant bounds
