# Research Findings for Proof Completion

## 1. Prime Splitting in CM Fields
In the extension $L/K = \mathbb{Q}(\zeta_p) / \mathbb{Q}(\zeta_p + \zeta_p^{-1})$:
- A rational prime $q \neq p$ splits in $L/K$ if its order $f$ in $(\mathbb{Z}/p\mathbb{Z})^\times$ is odd.
- It is inert if its order $f$ is even.
- The prime $p$ is ramified.

## 2. ClassGroup and Complex Conjugation
In Mathlib, `ClassGroup R` is equivalent to `(FractionalIdeal R⁰ K)ˣ ⧸ (toPrincipalIdeal R K).range`. 
To define a map on the Class Group induced by an automorphism (like complex conjugation `c`), we use the fact that `c` induces a map on fractional ideals and preserves the subgroup of principal ideals.
The map can be constructed using:
- `ClassGroup.equiv` (the equivalence to the quotient group of fractional ideals)
- `QuotientGroup.congr` (to lift the automorphism of fractional ideals to the quotient)

## 3. Parity Lemma (v_P(alpha/c(alpha)))
The parity lemma for a split prime $\mathfrak{p} = \mathfrak{P} c(\mathfrak{P})$ in a CM field relates the valuation of $\alpha/c(\alpha)$ to the local parity at the prime.
Specifically: $v_{\mathfrak{P}}(\alpha/c(\alpha)) = v_{\mathfrak{P}}(\alpha) - v_{c(\mathfrak{P})}(\alpha)$.
This parity is essential in defining the injectivity of the sign vector encoding map $\varphi: \epsilon \mapsto [J_\epsilon]$.

## 4. Sign Vector Encoding
The map $\varphi: \epsilon \mapsto [J_\epsilon]$ where $J_\epsilon = \prod \mathfrak{P}_j^{\epsilon_j} \bar{\mathfrak{P}}_j^{1-\epsilon_j}$ is injective on the Class Group class when the valuations at the chosen split primes distinguish the different ideals.
