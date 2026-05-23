# Detailed Specification: `gs_tower_levels` (Sawin Construction)

This document provides the exhaustive mathematical details required to formalize the Golod-Shafarevich tower construction from Sawin (arXiv:2605.20579).

## 1. Base Field Construction
*   **Set $T$**: A finite set of odd primes $\{q_1, \dots, q_m\}$.
*   **Parity Condition**: The number of $q \in T$ such that $q \equiv 3 \pmod 4$ must be **odd**.
*   **Quadratic Field $Q$**: $Q = \mathbb{Q}(\sqrt{\prod_{q \in T} q})$.
    *   The condition ensures $\prod q \equiv 3 \pmod 4$.
    *   The discriminant is $\Delta_Q = 4 \prod q$.
    *   $Q$ is a real quadratic field.

## 2. The Galois Group $G$
*   **Definition**: $G$ is the Galois group of the maximal pro-2 extension of $Q$ that is:
    1.  Everywhere unramified (at finite and infinite places).
    2.  Totally real.
    3.  Satisfies inertia degree bounds: for all $p \in S_{\mathbb{Q}}$, the inertia degree of any prime above $p$ is $\leq 2$ (and $\leq 1$ if $p$ is inert in $Q$).
*   **Generators**: $d(G) \geq \#T - 1$.
    *   This comes from the fact that $\mathbb{Q}(\{\sqrt{q} \mid q \in T\})$ is an unramified totally real extension of $Q$ with Galois group $(\mathbb{Z}/2\mathbb{Z})^{\#T-1}$.
*   **Relations**: $r(G) \leq d(G) + \#S_{\mathbb{Q}} + \#\{p \in S_{\mathbb{Q}} \mid p \text{ split in } Q\} + 2$.
    *   The term `+2` comes from the Euler characteristic of the unit group of the real quadratic field.

## 3. Golod-Shafarevich Criterion
*   **Infinitude**: $G$ is infinite if $r(G) \leq \frac{d(G)^2}{4}$.
*   **Sawin's explicit parameters**:
    *   $\#T = 13$, $\#S_{\mathbb{Q}} = 22$.
    *   No primes in $S_{\mathbb{Q}}$ split in $Q$.
    *   $d(G) \geq 12$.
    *   $r(G) \leq 12 + 22 + 0 + 2 = 36$.
    *   Criterion: $36 \leq \frac{12^2}{4} = 36$. (Equality holds, so $G$ is infinite).

## 4. Inertia Degree Control
*   The tower is constructed by quotienting out Frobenius elements (or their squares).
*   For $p \in S_{\mathbb{Q}}$ inert in $Q$, we quotient by the Frobenius element $\text{Frob}_{\mathfrak{p}}$.
*   For $p \in S_{\mathbb{Q}}$ ramified in $Q$, we quotient by the square of the Frobenius $\text{Frob}_{\mathfrak{p}}^2$.
*   Since $G$ remains infinite, there exists a tower level $F$ with degree $d = [F:\mathbb{Q}] \to \infty$.

## 5. Minkowski Embedding and Separation
*   **Field $K$**: $K = F(i)$. This is a CM field because $F$ is totally real.
*   **Lattice $\Lambda$**: $\Lambda = \Phi(D_0^{-1} \mathcal{O}_K)$, where $\Phi$ is the Minkowski embedding.
*   **Separation Bound**: For any $0 \neq v \in \Lambda$, $D_0 v$ is a nonzero algebraic integer in $K$.
    *   $\prod_{r=1}^f |\sigma_r(D_0 v)| = |N_{K/\mathbb{Q}}(D_0 v)|^{1/2} \geq 1$.
    *   $\prod_{r=1}^f |\sigma_r(v)| \geq D_0^{-f}$.
    *   This implies there exists at least one coordinate $r$ such that $|\sigma_r(v)| \geq D_0^{-1}$.
    *   **Lean Task**: Must prove the linear equivalence $\text{mixedSpace } K \simeq \text{Fin } f \to \mathbb{C}$ and reorder embeddings to ensure this holds for the first coordinate.

## 6. Mathematical Roadmap for Lean
1.  Define the profinite group $G$ as a limit of finite quotients.
2.  State the GS inequality as a theorem (or axiom for now).
3.  Implement the "Type Bridge":
    *   `Equiv (InfinitePlace K) (Fin (2f))`
    *   `LinearEquiv (mixedSpace K) (Fin f -> ℂ)` for totally complex fields.
4.  Prove the separation property using the product formula for algebraic integers.
