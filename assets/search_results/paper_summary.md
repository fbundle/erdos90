# OpenAI Paper: "Planar Point Sets with Many Unit Distances" — Full Summary

Source: `assets/unit-distance-proof.pdf` (18 pages, arXiv 2508.09480)

---

## Theorem 1.1 (Main Result)

There exists δ > 0 and infinitely many n with ν(n) ≥ n^{1+δ}.
This disproves the Erdős unit-distance conjecture.

---

## Section 2: Planar Point Sets from Number Fields

### Definition 2.1 (Admissible datum)
- Totally real number field L of degree f = [L:ℚ]
- CM field K = L(i), with nontrivial automorphism c over L (complex conjugation; c = overline in every complex embedding)
- Positive integer t (number of selected rational primes)
- Distinct rational primes q₁,...,qₜ ≡ 1 (mod 4), splitting completely in L
- Put Q = ∏_{b=1}^t q_b, D = Q²

**Split-prime structure**: Each q_b gives f prime ideals q of L, each with O_L/q ≅ F_{q_b}. Since q_b ≡ 1 (mod 4), x²+1 splits over F_{q_b}, so each q splits in K. Thus we get m = tf conjugate prime-ideal pairs:
  {𝔓_s, c𝔓_s},  s = 1,...,m

### Proposition 2.2
Let (L, K, t, q₁,...,qₜ, Q) be an admissible datum. Suppose h(K) ≤ H^f for some fixed H > 0. Then there is a set U ⊂ Q⁻²𝒪_K such that:
- Every u ∈ U satisfies N_{K/L}(u) = 1 (where N_{K/L}(u) = u·c(u) for K = L(i))
- Every u ∈ U satisfies |σ(u)| = 1 for every complex embedding σ: K → ℂ
- |U| ≥ exp{(t log 2 - log H) · f}

**Proof of Prop 2.2**:
1. For ε = (ε_s) ∈ {0,1}^m, define 𝔄_ε = ∏_{ε_s=1} 𝔓_s · ∏_{ε_s=0} c𝔓_s
2. These 2^m ideals occupy only h(K) ideal classes, so by pigeonhole, some fiber of ε ↦ [𝔄_ε] ∈ Cl(K) has size ≥ 2^m/h(K) ≥ 2^{tf}/H^f
3. Fix anchor η in such a fiber; for each ε in the fiber, 𝔄_ε · 𝔄_η⁻¹ is principal, choose α_ε ∈ K× with (α_ε) = 𝔄_ε · 𝔄_η⁻¹
4. Set u_ε = α_ε/c(α_ε)
5. For any complex embedding σ of K: σ(c(α)) = conj(σ(α)), so |σ(u_ε)| = |σ(α_ε)|/|conj(σ(α_ε))| = 1
6. Distinctness: valuation v_{𝔓_s}(u_ε) = 2(ε_s - η_s) distinguishes u_ε for distinct ε in the fiber
7. Q²u_ε ∈ 𝒪_K (poles are above q_b's with valuation at most 2), so U ⊂ Q⁻²𝒪_K □

### Lattice Construction (Section 2.1)
Choose f real embeddings σ_r: L → ℝ (one for each place), extend to σ_r: K → ℂ.
Define: Φ: K → V = ℂ^f,  Φ(x) = (σ₁(x),...,σ_f(x))
Identify the fractional ideal D⁻¹𝒪_K with the lattice Λ = Φ(D⁻¹𝒪_K) ⊂ ℂ^f.
Write U for its image Φ(U) ⊂ Λ.

Every coordinate of every u ∈ U has modulus 1 (from |σ(u)| = 1).

### Lemma 2.4 (Coset averaging)
Choose R > 1/2 so large that log ρ_R > -γ/2. Then some nonempty coset a + Λ satisfies:
  E_a ≥ e^{γf/2} · N_a
where γ := t log 2 - log H, ρ_R = a(R)/b(R) (disc overlap ratio).

### Lemma 2.5 (Projection injectivity)
The map π₁: X → ℂ is injective on X. Moreover, ν(P) ≥ (1/2) e^{γf/2} |P|.

**Proof**: If x, x' ∈ X with π₁(x) = π₁(x'), then x - x' = Φ(D⁻¹β) for some β ∈ 𝒪_K with σ₁(β) = 0. Since σ₁ is injective (field embedding), β = 0. □

### Lemma 2.6 (Size bound)
n = |P| ≤ e^{Bf}, where B = 2 log(4RD).

**Proof**: For 0 ≠ λ ∈ Λ, β = Q²λ is a nonzero algebraic integer, so:
  ∏_{r=1}^f |σ_r(λ)| = |N_{K/ℚ}(β)|^{1/2} · Q^{-2f} ≥ Q^{-2f}
So some coordinate of λ has modulus ≥ Q⁻² = D⁻¹. The packing gives |X| ≤ (4RD)^{2f}. □

### Theorem 2.3
Suppose there is a sequence of admissible data (L_j, K_j=L_j(i), q₁,...,qₜ) with:
- Same rational primes q₁,...,qₜ, degrees f_j = [L_j:ℚ] → ∞
- Constant H > 0 independent of j with h(K_j) ≤ H^{f_j}
- γ := t log 2 - log H > 0

Then there is a constant δ > 0 and infinitely many n with ν(n) ≥ n^{1+δ}.

---

## Section 3: Producing the Fields

### Proposition 3.2
Let r₁,...,rₗ be distinct rational primes ≡ 1 (mod 3). Let L_i be the cyclic cubic subfield of ℚ(ζ_{rᵢ}), put M = L₁···Lₗ. Let χᵢ be a cubic Dirichlet character of conductor rᵢ, and let F ⊂ M be the cyclic cubic field cut out by χ = χ₁···χₗ.
Then:
- Gal(M/ℚ) ≅ (ℤ/3ℤ)^ℓ,  Gal(M/F) ≅ (ℤ/3ℤ)^{ℓ-1}
- Writing D = ∏ rᵢ: |D_F| = D²
- M/F is everywhere unramified. All fields are totally real.

### Proposition 3.3 (Frattini quotient, [RZ10, Koc02, DdSMS99])
For a finitely generated pro-p group G: Φ(G) = ∩_M M = G^p[G,G].
d(G) = dim_{F_p} G/Φ(G). If g₁,...,g_k ∈ Φ(G) and N is their closed normal closure, then d(G/N) = d(G) and r(G/N) ≤ r(G) + k.

### Proposition 3.4 (Golod–Shafarevich inequality, [GS64, GS65, Koc02])
If a finite nontrivial pro-p group has generator rank d and relation rank r, then r > d²/4.
Equivalently, a nontrivial finitely generated pro-p group with r ≤ d²/4 is infinite.

### Proposition 3.5 (Shafarevich relation-rank estimate, [Sha63, Sha66, NSW08])
Let F be a totally real cubic field, ζ₃ ∉ F, G = Gal(F^{ur,3}/F) (Galois group of maximal everywhere-unramified pro-3 extension). Then r(G) ≤ d(G) + C₀ for an absolute constant C₀.

### Proposition 3.6 (Chebotarev density theorem, [Neu99 Ch.VII §13, Tsc26])
Let G = Gal(F^{ur,3}/F), E/F the Frattini quotient extension. For any positive integer t, after excluding any prescribed finite set of rational primes, there exist distinct q₁,...,qₜ which:
- Split completely in the normal closure over ℚ of E(i)
- Each q_b ≡ 1 (mod 4)
- Each q_b splits completely in F
- Every prime v | q_b of F has Frobenius in Φ(G)

### Proposition 3.7 (Class number bound, [Neu99 Ch.I §5, Lan94 Ch.V])
There is an absolute constant C_class > 0 such that every number field K satisfies:
  h(K) ≤ max{2, rd(K)}^{C_class · [K:ℚ]}
Equivalently, when rd(K) ≥ 2: h(K) ≤ rd(K)^{O([K:ℚ])} = |D_K|^{O(1)}.

This is the class-number consequence of Minkowski's ideal-class bound:
- Minkowski gives an integral ideal of norm X ≤ (C√A)^n in every ideal class
- The number of ideals of norm m is d_n(m) (n-fold divisor function)
- ∑_{m≤X} d_n(m) ≤ C^n X(1 + log X)^{n-1}/(n-1)!  [exponential in n when log X = O_A(n)]

### Proposition 3.8 (Field construction, full tower)
For all sufficiently large ℓ, set t = ⌊(ℓ-1)²/100⌋. Then one can find a number field F, distinct rational primes q₁,...,qₜ fixed independently of j, and fields F_j with F₀ = F, satisfying (writing f_j = [F_j:ℚ], K_j = F_j(i)):

(P1) F is totally real, cyclic cubic over ℚ, does not contain ζ₃, log rd(F) = O(ℓ log ℓ)
(P2) F = F₀ ⊂ F₁ ⊂ F₂ ⊂ ... with f_j → ∞, each F_j/F finite Galois everywhere unramified with 3-group Galois group
(P3) Every F_j is totally real, rd(F_j) = rd(F) (constant)
(P4) Each q_b ≡ 1 (mod 4) splits completely in every F_j
(P5) ∃ constant H_ℓ independent of j: rd(K_j) ≤ 2·rd(F), h(K_j) ≤ H_ℓ^{f_j}, log H_ℓ = O(ℓ log ℓ)
(P6) t log 2 - log H_ℓ > 0

**Proof sketch (4 steps)**:

Step 1: Construct F. Choose r₁,...,rₗ ≡ 1 (mod 3), Prop 3.2 gives F with |D_F| = D², Gal(M/F) ≅ (ℤ/3ℤ)^{ℓ-1}, everywhere unramified. Since F is totally real cubic and doesn't contain ζ₃, Prop 3.5 gives r(G) ≤ d(G) + C₀, and d(G) ≥ ℓ-1 (from the large unramified abelian extension M/F). log rd(F) = (1/3) log |D_F| = (2/3) ∑ log rᵢ = O(ℓ log ℓ) (prime number theorem in APs).

Step 2: Impose splitting. d = d(G), t = ⌊d²/100⌋ = ⌊(ℓ-1)²/100⌋. By Prop 3.6, choose q₁,...,qₜ with Frobenius in Φ(G). Let N = ⟨⟨{σ_v : v | q_b}⟩⟩ ⊴ G, set G̅ = G/N. Prop 3.3 gives d(G̅) = d, and r(G̅) ≤ r(G) + 3t ≤ d + C₀ + 3d²/100. For large d: r(G̅) < d²/4. By Prop 3.4, G̅ is infinite.

Step 3: Extract the tower. Choose descending chain G̅ = H₀ ⊃ H₁ ⊃ H₂ ⊃ ... of open normal subgroups with indices → ∞. Let F_j be the fixed fields. F_j/F is finite Galois, everywhere unramified, 3-group Galois group. The q_b's split completely in every F_j (Frobenius trivial in G̅, hence in each quotient).

Step 4: Class-number bounds. K_j = F_j(i). Since q_b ≡ 1 (mod 4), each prime v | q_b of F_j splits in K_j. Prop 3.7 gives h(K_j) ≤ H_ℓ^{f_j} with H_ℓ = (2 rd(F))^{2 C_class}, log H_ℓ = O(log rd(F)) = O(ℓ log ℓ). Finally, t ≥ (ℓ-1)²/200 while log H_ℓ = O(ℓ log ℓ), so t log 2 - log H_ℓ > 0 for large ℓ.

---

## Appendix A: Key Definitions

**Def A.4 (CM fields)**: A CM field is a totally imaginary quadratic extension K/K⁺ of a totally real field K⁺. The nontrivial automorphism is denoted c. For K = L(i) with L totally real, c becomes ordinary complex conjugation under every complex embedding, so elements u with u·c(u) = 1 have |σ(u)| = 1 in every complex embedding.

**Def A.7 (Frobenius elements)**: For finite Galois N/K and prime 𝔓 | p (unramified), Frob_{𝔓/p} ∈ Gal(N/K) acts on the residue field as x ↦ x^{|O_K/p|}. The prime p splits completely in N iff this Frobenius class is the identity.

**Prop A.13 (Minkowski class number bound)**: h(K) ≤ max{2, rd(K)}^{C_class · [K:ℚ]} with absolute constant C_class.

---

## Key Parameter Relations

- ℓ = parameter (chosen large), rᵢ = first ℓ primes ≡ 1 (mod 3)
- F = cyclic cubic field, D = ∏ rᵢ, |D_F| = D²
- log rd(F) = (2/3) ∑ log rᵢ = O(ℓ log ℓ) [by PNT in APs]
- G = Gal(F^{ur,3}/F), d(G) ≥ ℓ-1, r(G) ≤ d(G) + C₀
- t = ⌊(ℓ-1)²/100⌋, k = 3t primes of F above q₁,...,qₜ
- G̅ = G/N (kill Frobenius above q_b's): d(G̅) = d, r(G̅) < d²/4 for large ℓ
- G̅ infinite (Golod–Shafarevich) → infinite tower F = F₀ ⊂ F₁ ⊂ ...
- rd(F_j) = rd(F) [unramified extension preserves root discriminant]
- rd(K_j) ≤ 2·rd(F) [adjoining i: relative discriminant of K_j/F_j divides 4O_{F_j}]
- h(K_j) ≤ H_ℓ^{f_j}, H_ℓ = (2 rd(F))^{2 C_class}
- γ = t log 2 - log H_ℓ > 0 [since t ≳ ℓ² while log H_ℓ = O(ℓ log ℓ)]
- δ = γ/(4B) > 0 where B = 2 log(4RD)
