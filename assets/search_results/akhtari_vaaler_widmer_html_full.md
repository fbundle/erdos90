# Source: https://arxiv.org/html/2507.10387

# Effective Equidistribution of Norm One Elements in CM-Fields

**Authors:** Akhtari, Vaaler, Widmer
**arXiv:** 2507.10387

---

## Abstract

The paper studies equidistribution of elements in 𝒮_K — the maximal subgroup of K× that embeds into the unit circle under each complex embedding — for CM-fields, proving an effective equidistribution result with explicit convergence rates.

---

## Key Definitions

**𝒮_K**: The group {α ∈ K×: |α|_v = 1 for all archimedean places v}.

Also described as "the maximal subgroup of the multiplicative group K× that embeds into the unit circle under each complex embedding." This group serves as "an archimedean counterpart to the group of units of the ring of integers."

**CM-field**: A totally complex number field K containing a totally real subfield k of index 2.

**Weil Height H(α)**: The standard multiplicative height function on number fields, defined as H(α) = ∏_v max{1, |α|_v}^{[K_v:ℚ_v]/[K:ℚ]}.

**Norm One Group**: For CM-field K with maximal totally real subfield k, the group 𝒮_K equals ker(N_{K/k}: K× → k×).

**Lip(D,M,L)**: Sets whose boundary is covered by M maps satisfying Lipschitz condition with constant L.

**𝒮_K(ℐ,ℋ)**: The set of elements α ∈ 𝒮_K with H(α) ≤ ℋ such that the arguments of the embeddings σ_j(α) lie in the angular intervals ℐ_j.

**A_K**: The main term coefficient in the equidistribution formula, involving:
- Product over ramified primes P of (2N_k(P))/(N_k(P)+1)
- Normalization by √(N_k(D_{K/k}))
- Class number h_k, regulator R_k, and ζ_k(2)

**𝕌_k**: The unit lattice ℓ(𝒪_k×) in logarithmic coordinates.

**σ₁,...,σ_N**: Independent embeddings of K into ℂ (the complex embeddings, one per pair).

**τ**: The non-trivial automorphism of K fixing k (complex conjugation on K).

**ℐ = ℐ₁ × ... × ℐ_N**: Product of angular intervals (ℐ_j ⊆ [0,2π)).

**S_F(ℐ*;T)**: The fundamental counting domain {𝐱 = (x_n) ∈ (ℂ×)^N: (2log|x_n|)_n ∈ F(T), (arg(x_n))_n ∈ ℐ*}.

---

## Main Theorems

### Theorem 1.1 (Effective Equidistribution — Main Result)

For a CM-field K of degree 2N, there exists C_K > 0 depending only on K such that for all ℋ ≥ 2:

|# 𝒮_K(ℐ,ℋ) − A_K |ℐ| ℋ^{2N}| ≤ C_K ℋ^{2N-1} ℒ

where ℒ = log ℋ if N = 1, and ℒ = 1 if N ≥ 2.

### Theorem 2.1 (Blanksby-Loxton)

"A number field K of degree d > 1 is a CM-field if and only if K = ℚ(α) for some α ∈ 𝒮_K."

---

## Propositions

### Proposition 1.1

Let K be a number field. If ℚ(𝒮_K) is not a CM-field, then 𝒮_K = {±1}. If ℚ(𝒮_K) is a CM-field, then 𝒮_K/Tor(K×) is a free abelian group of countably infinite rank.

### Proposition 1.2

If K is a CM-field with maximal totally real subfield k, then 𝒮_K is the kernel of the norm map N_{K/k}: K× → k×.

### Proposition 2.1

For CM-field K with maximal totally real subfield k, 𝒮_K equals the kernel of N_{K/k}: K× → k×.

**Proof (Forward direction):** Let α ∈ ker N_{K/k}. Using τ = σ^{-1} ∘ ρ ∘ σ (the Galois involution) and N_{K/k}(α) = α · τ(α) = 1:

Applying σ to both sides: σ(α) · ρ(σ(α)) = |σ(α)|² = 1

for any embedding σ: K → ℂ. Thus |σ(α)| = 1 for all embeddings, so α ∈ 𝒮_K.

**Proof (Backward direction):** If β ∈ 𝒮_K, then |σ(β)| = 1 for all σ. Thus:

σ(β) · ρ(σ(β)) = 1 for all σ.

Applying σ^{-1}: β · τ(β) = 1, so N_{K/k}(β) = 1, meaning β ∈ ker N_{K/k}.

---

## Corollaries

### Corollary 1.1

Under conditions of Theorem 1.1, the discrepancy D_ℋ(𝒮_K) ≤ C'_K (ℒ/ℋ), showing elements become equidistributed on the unit circle.

---

## Lemmas

### Lemma 2.1 (Shimura's Characterization)

"A number field K is a CM-field if and only if there exists a non-trivial automorphism τ of K such that σ ∘ τ = ρ ∘ σ for all homomorphisms σ: K → ℂ" (where ρ is complex conjugation).

### Lemma 2.2 (Shimura)

The composite of finitely many CM-fields is a CM-field.

### Lemma 2.3

𝒮_K ≠ {±1} iff ℚ(𝒮_K) is a CM-field.

### Lemma 3.1 (Free Abelian Structure)

For CM-field K, 𝒮_K/Tor(K×) is a free abelian group of countably infinite rank.

**Proof:** The quotient 𝒮_K/Tor(K×) is an abelian group. The logarithmic Weil height h: 𝒢_K = K×/Tor(K×) → [0,∞) satisfies four properties:

(i) h(α) ≥ 0 with equality iff α = 1
(ii) h(α^m) = |m|h(α) for m ∈ ℤ
(iii) h(αβ) ≤ h(α) + h(β)
(iv) There exists ε(K) > 0: h(α) ≥ ε(K) for all α ≠ 1

These conditions define a discrete norm on the group. A fundamental theorem states that any abelian group admitting a discrete norm is free.

Since 𝒮_K/Tor(K×) ⊆ 𝒢_K inherits the discrete norm structure, it must be a free group. Brandis proved K×/k× is not finitely generated; since ψ̂: K×/k× → 𝒮_K is an isomorphism, 𝒮_K/Tor(K×) has countably infinite rank.

### Lemma 4.1 (Lattice Point Counting)

For lattice Λ in ℝ^D with boundary ∂S in Lip(D,M,L):

|#(Λ∩S) − Vol(S)/det(Λ)| ≤ D^{3D²/2} M ((L/λ₁)^{D-1} + 1*(S∩Λ))

where λ₁ is the first successive minimum of Λ.

### Lemma 4.2 (Simplified Lattice Counting)

If S has boundary in Lip(D,M,L), is contained in a closed ball of radius L about origin, and origin ∉ S, then:

|#(Λ∩S) − Vol(S)/det Λ| ≤ 2D^{3D²/2} M (L/λ₁)^{D-1}

**Proof:** Employs the Lipschitz boundary condition. By covering ∂S with M parametric maps with Lipschitz constant L, the surface area is bounded. Using Gauss-Bonnet on each piece and summing, the number of lattice points "near" the boundary is at most D^{3D²/2} M (L/λ₁)^{D-1}. When S ∩ Λ ≠ ∅, add 1 for interior points; otherwise 1* = 0. When origin is excluded and S is in a ball, S cannot contain lattice points in its interior, so the error becomes purely boundary-dependent: 2D^{3D²/2} M (L/λ₁)^{D-1}.

### Lemma 5.1 (Lipschitz Boundary)

The set S_F(ℐ*;1) is contained in a closed euclidean ball of radius L = L(K), its boundary is in Lip(2N,M,L) with M = M(N), and origin ∉ S_F(ℐ*;1).

**Proof:**

**Boundedness:** If 𝐱 ∈ S_F(ℐ*;1), then |x_n|² = exp(z_n) where z_n ∈ F lies in a parallelotope of diameter O(N·R_k). Thus |x_n|² ≤ exp(N·c_N·R_k) = L₀² for L₀ = (N·exp(N·c_N·R_k))^{1/2}.

**Lipschitz boundary:** The boundary ∂(S_F(ℐ*;1)) consists of:
1. Points with (2log|x_n|)_n on ∂F: Parametrized by Lipschitz maps from [0,1]^{2N-1} using reduction theory of 𝕌_k.
2. Points with (arg(x_n))_n on ∂ℐ*: 2^N Lipschitz maps, each sending t_m ∈ [0,1] to t_m·L₀·exp(i·γ) for boundary points γ ∈ ∂ℐ*.

Each map satisfies |ϕ(𝐱) - ϕ(𝐲)| ≤ L|𝐱 - 𝐲| with L ≪_K 1 from explicit complex analysis estimates.

### Lemma 5.2 (Volume Calculation)

S_F(ℐ*;1) is measurable with Vol(S_F(ℐ*;1)) = |ℐ| R_k / (2^N ω_k).

**Proof:** The volume is computed by integrating over the fundamental domain:

Vol(S_F(ℐ*;1)) = ∫_F ∫_{ℐ*} |det(Jacobian)| dθ dz

The Jacobian of the map (z₁,...,z_N, θ₁,...,θ_N) ↦ (|z₁|e^{iθ₁},...,|z_N|e^{iθ_N}) involves factors:
- From ℐ*: |ℐ| (product of interval lengths)
- From F: Vol(F) = √N · R_k (using the reduced basis)
- Jacobian factor: 1/(2^N · ω_k)

This yields Vol(S_F(ℐ*;1)) = |ℐ| R_k / (2^N ω_k).

---

## Hilbert's Theorem 90 Application

The homomorphism ψ: K× → K× defined by ψ(β) = β/τ(β) has image equal to ker(N_{K/k}).

The map ψ̂: K×/k× → 𝒮_K is an isomorphism.

---

## Proof Strategy (Overview of Sections 4-8)

### Step 1 — Structure via Hilbert 90 (Section 2-3)

From Proposition 2.1, 𝒮_K equals ker N_{K/k}. The homomorphism ψ(β) = β/τ(β) (where τ is the Galois involution) satisfies ker ψ = k× and im ψ = ker N_{K/k} = 𝒮_K by Hilbert's Theorem 90. This gives isomorphism ψ̂: K×/k× → 𝒮_K.

### Step 2 — Fundamental Domain Construction (Section 6)

The goal is to construct a fundamental domain for K× under the action of k×. Elements of K× are identified with their Minkowski embedding 𝝈(β) = (σ₁(β),...,σ_N(β)) ∈ ℂ^N.

For each class representative C_j from the class group Cl_k, and each ramified prime P_i, we build a region D_{j,I} parametrizing elements whose fractional ideal lies in a prescribed class and whose prime factorization avoids certain ramified primes up to a given bound.

### Step 3 — Height Function Parametrization (Section 5)

For T ≥ 1, define F(T) = F + (2,...,2)(-∞, log T] where F is a fundamental domain for the unit lattice 𝕌_k = ℓ(𝒪_k×) acting on Σ = {(z_n): Σz_n = 0}.

The counting domain is:
S_F(ℐ*;T) = {𝐱 = (x_n) ∈ (ℂ×)^N: (2log|x_n|)_n ∈ F(T), (arg(x_n))_n ∈ ℐ*}

By Lemma 5.2: Vol(S_F(ℐ*;1)) = |ℐ| R_k / (2^N ω_k).

### Step 4 — Lattice Point Counting (Section 7)

The Minkowski embedding maps 𝒪_K into the lattice Λ = 𝝈(𝒪_K) ⊂ ℂ^N ≅ ℝ^{2N}.

Elements of 𝒮_K(ℐ,ℋ) correspond to lattice points in a sieved version of S_F(ℐ*;T) where T ≈ ℋ^{2N}, accounting for:
- Unit group action (sieving by units)
- Class group action (sieving by class representatives)
- Ramification conditions

### Step 5 — Error Term Analysis

Lemma 4.2 applied to the geometry of S_F(ℐ*;T) yields:

Error ≤ 2D^{3D²/2} M (L/λ₁)^{2N-1}

where:
- D = 2N (complex embedding dimension)
- L = L(K) (Lipschitz constant from Lemma 5.1)
- λ₁ is the Hermite constant of 𝝈(𝒪_K)

The Hermite constant satisfies λ₁ ≥ λ₁(𝕌_k) ≫_K 1, yielding (L/λ₁)^{2N-1} = O(T^{1-1/N}) = O(ℋ^{2N-1}).

### Step 6 — Main Term Computation (Section 8)

The constant A_K encodes:
- Discriminant factors: ∏_{P|D_{K/k}} 2N_k(P)/(N_k(P)+1) · 1/√N_k(D_{K/k})
- Analytic invariants: h_k R_k / (ω_k ζ_k(2) |Δ_k|)

These arise from applying the Poisson summation formula over the class group and unit lattice.

**Section 8 (Final Count):** By Möbius inversion over the class group and Inclusion-Exclusion over ramified primes:

# 𝒮_K(ℐ,ℋ) = Σ_{I⊆{1,...,s}} μ(I) Σ_{j=1}^h #{Λ ∩ (C_j^{-1} · S_F(ℐ*; ℋ^{1/2N}))}

Applying Lemma 4.2 to each term:
#{Λ ∩ S} = Vol(S)/det Λ + O(ℋ^{2N-1})

The volume factor combines from all sieving parameters to yield the main term A_K |ℐ| ℋ^{2N}, while the error estimates (with careful tracking through the sieve) accumulate to C_K ℋ^{2N-1} ℒ.

---

## Significance

This work improves upon prior results by Petersen and Sinclair for imaginary quadratic fields by providing the first effective equidistribution theorem for general CM-fields with explicit error terms. The method uses purely geometric/combinatorial techniques (lattice point counting via Lipschitz boundary analysis) rather than analytic techniques.

**Petersen-Sinclair (2011):** "Ineffective equidistribution result has been proven...in the case of imaginary quadratic fields."

The paper extends this to all CM-fields with explicit error terms.

---

## Notation Conventions

- σ₁,...,σ_N: Independent complex embeddings of K (one from each conjugate pair)
- τ: Non-trivial automorphism fixing k (complex conjugation)
- arg(x): Argument of x ∈ ℂ× lying in [0,2π)
- ℐ = ℐ₁ × ... × ℐ_N: Product of angular intervals
- 𝕌_k = ℓ(𝒪_k×): Unit lattice in logarithmic coordinates
- h_k: Class number of k
- R_k: Regulator of k
- ω_k: Number of roots of unity in k
- D_{K/k}: Relative discriminant of K/k
