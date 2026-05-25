# Valuation Arithmetic for α/c(α) Membership

## 1. Goal
Prove that for $\alpha \in K^\times$ satisfying $(\alpha)J(\varepsilon_1) = J(\varepsilon_2)$, the element $Q^2 \cdot \alpha/c(\alpha)$ is an algebraic integer ($Q^2 \cdot \alpha/c(\alpha) \in \mathcal{O}_K$), where $Q = \prod q_j$ is the product of rational primes below the split primes in the construction.

## 2. Parity Argument
In a CM field $K/F$, a split prime $q$ of $F$ in $K$ has the form $q \mathcal{O}_K = \mathfrak{P} \bar{\mathfrak{P}}$ with $\mathfrak{P} \neq \bar{\mathfrak{P}}$. Complex conjugation $c$ acts on these primes by $c(\mathfrak{P}) = \bar{\mathfrak{P}}$.

The ideal $J(\varepsilon)$ is defined as a product of exactly one prime from each split pair $(\mathfrak{P}_j, \bar{\mathfrak{P}}_j)$.
Let $v_{\mathfrak{P}}$ denote the valuation at the prime ideal $\mathfrak{P}$.

If $(\alpha) J(\varepsilon_1) = J(\varepsilon_2)$, then for any split prime $\mathfrak{P}_j$:
$$v_{\mathfrak{P}_j}(\alpha) = v_{\mathfrak{P}_j}(J(\varepsilon_2)) - v_{\mathfrak{P}_j}(J(\varepsilon_1)) \in \{0, 1, -1\}$$
$$v_{\bar{\mathfrak{P}}_j}(\alpha) = v_{\bar{\mathfrak{P}}_j}(J(\varepsilon_2)) - v_{\bar{\mathfrak{P}}_j}(J(\varepsilon_1)) \in \{0, 1, -1\}$$

Since $J(\varepsilon)$ contains exactly one of $\mathfrak{P}_j$ or $\bar{\mathfrak{P}}_j$:
- If $\mathfrak{P}_j \in J(\varepsilon_2)$, then $v_{\mathfrak{P}_j}(J(\varepsilon_2)) = 1$ and $v_{\bar{\mathfrak{P}}_j}(J(\varepsilon_2)) = 0$.
- If $\mathfrak{P}_j \notin J(\varepsilon_2)$, then $v_{\mathfrak{P}_j}(J(\varepsilon_2)) = 0$ and $v_{\bar{\mathfrak{P}}_j}(J(\varepsilon_2)) = 1$.

Thus, $v_{\mathfrak{P}_j}(\alpha) - v_{\bar{\mathfrak{P}}_j}(\alpha)$ is always an even integer in $\{0, 2, -2\}$.
Specifically, $v_{\mathfrak{P}_j}(\alpha/c(\alpha)) = v_{\mathfrak{P}_j}(\alpha) - v_{\mathfrak{P}_j}(c(\alpha)) = v_{\mathfrak{P}_j}(\alpha) - v_{\bar{\mathfrak{P}}_j}(\alpha) \in \{0, 2, -2\}$.

## 3. Integrality via Scaling
If $v_{\mathfrak{P}_j}(\alpha/c(\alpha)) \ge -2$ for all split primes $\mathfrak{P}_j, \bar{\mathfrak{P}}_j$, and $v_P(\alpha/c(\alpha)) \ge 0$ for all other primes (which do not divide $J$ or $c(J)$), then:
- At any split prime $\mathfrak{P}_j$ above $q_j$, we have $v_{\mathfrak{P}_j}(q_j^2 \cdot \alpha/c(\alpha)) = 2 + v_{\mathfrak{P}_j}(\alpha/c(\alpha)) \ge 2 - 2 = 0$.
- For any other prime $P$ not above some $q_j$, $v_P(Q^2 \cdot \alpha/c(\alpha)) = v_P(\alpha/c(\alpha)) \ge 0$.

Thus $Q^2 \cdot \alpha/c(\alpha)$ has non-negative valuation at all prime ideals, which implies it is an algebraic integer.

## 4. Mathlib API (v4.30)

- **Valuation on Fractional Ideals**: `FractionalIdeal.count K v I` in `RingTheory/DedekindDomain/Factorization.lean`.
- **Valuation Multiplicativity**: `count_mul` and `count_pow`.
- **Integrality Criterion**: `mem_integers_of_valuation_le_one` in `RingTheory/DedekindDomain/AdicValuation.lean`.
  - Signature: `(x : K) (h : ∀ v : HeightOneSpectrum R, v.valuation K x ≤ 1) : x ∈ (algebraMap R K).range`
  - Note: `HeightOneSpectrum.valuation` is multiplicative; `v.valuation K x ≤ 1` is equivalent to the additive valuation being $\ge 0$.
- **Action on Ideals**: `IsCMField.complexConj` and `conjIdeal` (defined in `Erdos90/CMField/Basic.lean`).
