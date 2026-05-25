# Minkowski Class-Number Bound for Cyclotomic Fields

## 1. Mathematical Background

For a number field $K$ of degree $n = [K : \mathbb{Q}]$, let $r_1$ be the number of real embeddings and $r_2$ the number of pairs of complex embeddings ($n = r_1 + 2r_2$). Let $|\Delta_K|$ be the absolute discriminant of $K$.

### Minkowski Bound ($M_K$)
The Minkowski bound $M_K$ is defined such that every ideal class in $\text{Cl}(K)$ contains an integral ideal $\mathfrak{a}$ with norm:
$$N(\mathfrak{a}) \le M_K = \frac{n!}{n^n} \left( \frac{4}{\pi} \right)^{r_2} \sqrt{|\Delta_K|}$$

### Cyclotomic Field $\mathbb{Q}(\zeta_p)$
For $K = \mathbb{Q}(\zeta_p)$ (where $p$ is an odd prime):
- Degree: $n = p-1$.
- Signature: $r_1 = 0$, $r_2 = (p-1)/2$.
- Discriminant: $|\Delta_K| = p^{p-2}$.
- $f = (p-1)/2$ (number of complex places).

Substituting these into the Minkowski bound:
$$M_K = \frac{(p-1)!}{(p-1)^{p-1}} \left( \frac{4}{\pi} \right)^{(p-1)/2} \sqrt{p^{p-2}}$$

Using Stirling's approximation $(n! \approx (n/e)^n \sqrt{2\pi n})$:
$$M_K \approx \sqrt{2\pi(p-1)} \left( \frac{4}{\pi e^2} \right)^{(p-1)/2} p^{(p-2)/2}$$
Since $4 / (\pi e^2) \approx 4 / (3.14 \cdot 7.39) \approx 0.17$, the factor $(0.17)^{f}$ is very small, but $p^f$ grows quickly.
$$M_K \approx \sqrt{2\pi(2f)} (0.17)^f p^{f - 1/2}$$

## 2. Quantitative Class Number Bound

The class number $h_K$ is bounded by the number of integral ideals with norm $\le M_K$.
A refined bound for the number of ideals $A(X)$ with norm $\le X$ in a field of degree $n$ is:
$$h_K \le \frac{1}{(n-1)!} M_K (\log M_K + n - 1)^{n-1}$$

For $K = \mathbb{Q}(\zeta_p)$, we have $\log M_K \approx f \log p$.
Plugging this in:
$$h_K \le \frac{1}{(2f-1)!} M_K (f \log p + 2f - 1)^{2f-1} \approx \frac{1}{(2f/e)^{2f}} M_K (f (\log p + 2))^{2f} = \left( \frac{e f (\log p + 2)}{2f} \right)^{2f} M_K = \left( \frac{e}{2} (\log p + 2) \right)^{2f} M_K$$
Since $M_K \approx (0.41 \sqrt{p})^{2f}$, we get:
$$h_K \le ( 0.55 \sqrt{p} (\log p + 2) )^{p-1}$$
$$\log h_K \le (p-1) \left( \frac{1}{2} \log p + \log \log p + \text{const} \right)$$
Dividing by $f = (p-1)/2$:
$$\frac{\log h_K}{f} \le \log p + 2 \log \log p + C'$$

This shows that $h_K \le \exp(C \cdot f \log f)$ is a more natural bound, but since the paper uses a sequence of fields where $\text{rd}_F$ is related to $p$ (for cyclotomic fields), the bound $\log h_K / f \le \log_H$ where $\log_H$ depends on the root discriminant is exactly what is needed.

## 3. Mathlib API (v4.30)

- **Minkowski Bound Definition**: `M K` in `NumberTheory/NumberField/ClassNumber.lean`.
- **Minkowski Bound Theorem**: `exists_ideal_in_class_of_norm_le` in `NumberTheory/NumberField/ClassNumber.lean`.
- **Cyclotomic Discriminant**: `IsCyclotomicExtension.discr_odd_prime` in `NumberTheory/Cyclotomic/Discriminant.lean`.
  - Signature: `discr K (hζ.powerBasis K).basis = (-1) ^ ((p - 1) / 2) * p ^ (p - 2)`
- **Class Number Formula**: Not directly available as a bound, but `Fintype (ClassGroup (𝓞 K))` is proved in `NumberTheory/ClassNumber/Finite.lean`.
