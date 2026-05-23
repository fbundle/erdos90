# Mathematical Handover Summary for Lean 4 Coder AI

This document provides the high-density mathematical "recipe" required to replace the remaining `sorry` blocks in the Erdős Problem 90 formalization.

## 1. Goal: Infinite Golod–Shafarevich Tower (`gs_tower_levels`)
Construct an infinite tower of totally real fields $F_j$ over $Q$ unramified at all finite places, where $S_{\mathbb{Q}}$ primes have inertia degree $\leq 2$.

### Parameters (Sawin Construction)
*   **Base Field $Q$**: $\mathbb{Q}(\sqrt{\prod_{q \in T} q})$ where $T = \{3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43\}$.
*   **Parity**: 7 primes in $T$ are $\equiv 3 \pmod 4$ (odd count), ensuring $\prod q \equiv 3 \pmod 4$ and $Q$ is real quadratic.
*   **Group $G$**: Maximal unramified pro-2 extension of $Q$ where:
    *   $\text{Inertia}(p) \leq 1$ if $p \in S_{\mathbb{Q}}$ is inert in $Q$.
    *   $\text{Inertia}(p) \leq 2$ if $p \in S_{\mathbb{Q}}$ is ramified/split in $Q$.
*   **The GS Bound**:
    *   $d(G) \ge \#T - 1 = 12$.
    *   $r(G) \le d(G) + \#S_{\mathbb{Q}} + 2 = 12 + 22 + 2 = 36$.
    *   $r(G) \le d(G)^2/4$ holds ($36 \le 144/4$).
*   **Lattice $\Lambda$**: Image of $D_0^{-1} \mathcal{O}_{F_j(i)}$ under Minkowski embedding $\Phi$.
*   **Separation**: Non-zero $v \in \Lambda \implies \prod |\sigma_r(v)| \ge D_0^{-f}$ (Product Formula).

## 2. Goal: CM Class-Group Pigeonhole (`exists_cm_class_group_data`)
Find many norm-1 elements in the lattice by mapping sign vectors to the class group.

### The Construction
*   **Sign Vectors**: $E = \{0, 1\}^m$ where $m$ is the number of prime ideal pairs above $S_{\mathbb{Q}}$.
*   **Class Map $\phi$**: $\phi(\epsilon) = [\prod_{s=1}^m \mathfrak{P}_s^{\epsilon_s} (c\mathfrak{P}_s)^{1-\epsilon_s}]$.
*   **Cardinality Ratio**: $|E|/|G| \ge \exp(\gamma f) + 1$. Requires **Louboutin's Bound**:
    $$h^-(K) \le 8 \operatorname{rd}_{K/F}^2 \left( \frac{e \sqrt{\operatorname{rd}_{K/F}} \log(\operatorname{rd}_{K/F})}{4\pi} \right)^f$$
*   **Injectivity (`mk_unit_inj`)**:
    1.  If $\text{unit}(\epsilon_2) = \text{unit}(\epsilon_3)$, then $\alpha_2 / \alpha_3 \in K^+ = F$.
    2.  Ideal $(\alpha_2 / \alpha_3)$ is an ideal in $F$, so valuations at split primes $\mathfrak{P}$ must be even.
    3.  Valuation of constructed ideal $\mathfrak{A}_{\epsilon_2} \mathfrak{A}_{\epsilon_3}^{-1}$ at $\mathfrak{P}_s$ is $\epsilon_{2,s} - \epsilon_{3,s} \in \{-1, 0, 1\}$.
    4.  Only even value is $0$, thus $\epsilon_{2,s} = \epsilon_{3,s} \implies \epsilon_2 = \epsilon_3$.

## 3. Goal: The Exponent $\delta \approx 0.014114$
*   **Parameters**: $R = 72$, $k_p$ values in `sawin_explicit_parameters.md`.
*   **Calculation**: Numerator $\approx 3.8822$, Denominator $\approx 275.055$.
*   **Result**: $\delta > 0.014$, disproving the conjecture.

---
**Implementation Priority for Coder AI**:
1.  Define **Type Bridge**: `mixedSpace K ≃ₗ[ℝ] (Fin f → ℂ)` for totally complex fields.
2.  Prove **IsAddFundamentalDomain transport** across LinearEquiv.
3.  Implement **Valuation Parity Lemma** for CM extensions to close `mk_unit_inj`.
4.  Formalize **GS parameters** ($d, r$) as a concrete assumption.
