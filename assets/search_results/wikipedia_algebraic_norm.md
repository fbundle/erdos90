# Source: https://en.wikipedia.org/wiki/Algebraic_norm

## Note: 404 / Redirect

The URL https://en.wikipedia.org/wiki/Algebraic_norm returned HTTP 404 (page does not exist).

The corresponding Wikipedia article is at: https://en.wikipedia.org/wiki/Field_norm

---

## Field Norm (Wikipedia article at https://en.wikipedia.org/wiki/Field_norm)

### Overview

In mathematics, the **field norm** (also called algebraic norm) is a mapping defined in field theory that "maps elements of a larger field into a subfield."

### Formal Definition

Let K be a field and L a finite algebraic extension of K. L functions as a finite-dimensional vector space over K.

For an element α in L, multiplication by α (denoted m_α) creates a K-linear transformation on L (viewed as a K-vector space). The norm N_{L/K}(α) is defined as:

> N_{L/K}(α) = det(m_α)

the determinant of this linear transformation.

**For Galois extensions:** If L/K is Galois with group G = Gal(L/K), then:

> N_{L/K}(α) = ∏_{σ ∈ G} σ(α)

**For general extensions:** For nonzero α with minimal polynomial f(x) = x^d + a_{d-1}x^{d-1} + ... + a₀ over K (where d = [K(α):K]), and [L:K(α)] = m:

> N_{L/K}(α) = ((-1)^d · a₀)^m

### Key Examples

**Quadratic fields:** For Q(√a)/Q where a is square-free:
- N(x + y√a) = x² - ay²
- This is the determinant of the matrix [[x, ay], [y, x]]

**Q(√2):** N(1 + √2) = (1+√2)(1-√2) = 1 - 2 = -1

**Complex numbers C/R:** N_{C/R}(x + iy) = x² + y². The norm sends x+iy to x²+y², since complex conjugation generates Gal(C/R).

**Finite fields:** For GF(q^n)/GF(q): N(α) = α^((q^n - 1)/(q - 1))

### Properties

1. **Multiplicativity:** N_{L/K}(αβ) = N_{L/K}(α) · N_{L/K}(β). Thus N is a group homomorphism L^× → K^×.

2. **Scaling:** N_{L/K}(aα) = a^[L:K] · N_{L/K}(α) for a ∈ K.

3. **Tower formula:** For fields K ⊂ L ⊂ M: N_{M/K} = N_{L/K} ∘ N_{M/L}.

4. **Units:** An element α ∈ O_L (ring of integers) is a unit if and only if N_{L/K}(α) = ±1 (for K = Q) or is a unit in O_K.

5. **Integrality:** If α ∈ O_L then N_{L/K}(α) ∈ O_K.

### Connection to Ideal Norms

For an ideal I of O_K in a number field K/Q, the **ideal norm** is:
> N(I) = |O_K / I| = [O_K : I]

Properties:
- N(IJ) = N(I) · N(J)
- For a principal ideal (α): N((α)) = |N_{K/Q}(α)|
- For a prime ideal P above rational prime p: N(P) = p^f where f = [O_K/P : F_p] is the residue degree

### Norm-1 Elements and CM Fields

For a CM field K (a totally imaginary quadratic extension of a totally real field), with complex conjugation τ ∈ Gal(K/K⁺):

The **CM norm condition** N_{K/K⁺}(α) = 1 is equivalent to α/τ(α) = 1, i.e., α·ᾱ = 1 (where bar denotes complex conjugation).

In the Minkowski embedding φ: K → ℂ^f (f = [K:Q]/2 for totally complex K), norm-1 elements under the CM norm satisfy |φ_w(α)| = 1 for all complex places w.

This is the key property used in the Erdős unit distance proof: elements of norm 1 under the CM norm map to points on the unit circle in each complex coordinate of the Minkowski embedding.

### Norm in Lean 4 / Mathlib

In Mathlib:
- `Algebra.norm K : L →*₀ K` — the norm as a monoid-with-zero homomorphism
- `RingOfIntegers.norm K : (𝓞 L) →* (𝓞 K)` — restriction to rings of integers
- `RingOfIntegers.dvd_norm` — in Galois extensions, x divides algebraMap(norm K x)
- `RingOfIntegers.isUnit_norm_of_isGalois` — unit iff norm is unit (in Galois case)
- `RingOfIntegers.isUnit_norm` — unit iff norm is unit (for characteristic 0 base)
- `RingOfIntegers.norm_norm` — N_{M/K} = N_{L/K} ∘ N_{M/L}
- `Algebra.coe_norm_int` — coercion from ℤ-norm to ℚ-norm

### Norm at Places (Mathlib: normAtPlace)

For number fields in Mathlib, there is also the place-wise norm:
- `normAtPlace w x` — the norm at an infinite place w of K
- For real places: `normAtPlace w x = |embedding_w x|`
- For complex places: `normAtPlace w x = ‖embedding_w x‖²` (squared absolute value)

This appears in `NumberFieldDeep_CM.lean` in the project:
- `normAtPlace_mixedEmbedding_cm_div_conj_eq_one` — normAtPlace = 1 at each complex place
- `mixedEmbedding_cm_div_conj_complex_norm_one` — ‖.2 w‖ = 1 per complex place

### Related Wikipedia Articles
- Field norm: https://en.wikipedia.org/wiki/Field_norm
- Norm form: https://en.wikipedia.org/wiki/Norm_form (homogeneous form from field norm)
- Algebraic number theory: https://en.wikipedia.org/wiki/Algebraic_number_theory
- Class group: https://en.wikipedia.org/wiki/Ideal_class_group
