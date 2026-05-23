# Sawin's Explicit Parameters for $\delta \approx 0.014$

This document lists the specific primes and parameters used in Sawin (arXiv:2605.20579) to achieve the explicit lower bound $\nu(n) \geq n^{1.014114}$.

## 1. Prime Sets
*   **Set $T$ (Base field construction)**:
    $\{3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43\}$
    *   Total: 13 primes.
    *   Primes $\equiv 3 \pmod 4$: $\{3, 7, 11, 19, 23, 31, 43\}$ (7 primes - ODD).
*   **Set $S_{\mathbb{Q}}$ (Unit distance primes)**:
    $\{2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 47, 71, 79, 97, 101, 107, 109, 139, 151, 163, 167, 179\}$
    *   Total: 22 primes.

## 2. Group Theory Parameters
*   $d(G) \geq 12$.
*   $r(G) \leq 12 + 22 + 0 + 2 = 36$.
*   $r(G) \leq d(G)^2 / 4 \implies 36 \leq 144 / 4 = 36$.

## 3. Calculation of $\delta$
Sawin uses the following formula (Theorem 3.1 specialized):
$$ \delta = \frac{ \log(1 - 1/R) + \frac{1}{2} \log(2\pi/e) + \sum \frac{1}{2 e_p f_p} \log(k_p + 1) - \frac{1}{4} \log \lambda - \frac{1}{2} \log \log \lambda }{ \log ( 2R \prod p^{k_p / 2 e_p} + 1 ) } $$

With values:
*   $R = 72$.
*   $k(2)=50, k(3)=31, k(5)=21, k(7)=17, k(11)=14, k(13)=13, k(17)=12, k(19)=11, k(23)=10, k(29)=10$.
*   $k(47)=8$.
*   $k(71 \dots 109)=7$.
*   $k(139 \dots 179)=6$.
*   $\lambda = \operatorname{rd}_{K/F} = \sqrt{\Delta_Q} = \sqrt{4 \prod_{q \in T} q}$.

**Result**:
*   Numerator $\approx 3.8822$.
*   Denominator $\approx 275.055$.
*   $\delta \approx 0.014114$.

## 4. Relevance for Lean Formalization
These parameters can be used to construct a **concrete instance** of the theorem in Lean, rather than just an existential proof. By proving that these specific primes satisfy the GS criterion, one can avoid formalizing the entire general theory of Golod-Shafarevich and instead focus on this specific tower.
