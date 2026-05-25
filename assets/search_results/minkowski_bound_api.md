# Gap S2: Minkowski Class-Number Bound

## Q5: `exists_ideal_in_class_of_norm_le`

**File Path**: `Mathlib/NumberTheory/NumberField/ClassNumber.lean`

**Theorem Statement**:
```lean
theorem exists_ideal_in_class_of_norm_le (C : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = C ∧
      absNorm (I : Ideal (𝓞 K)) ≤ M K
```
- **Type of `M K`**: `ℝ`.
- **Purpose**: It gives a representative integral ideal `I` for any class `C` such that the norm of `I` is at most the Minkowski constant `M K`.
- **Definition of `M K`**:
  ```lean
  local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
    ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)
  ```

## Q6 & Q8: Cyclotomic Discriminant

**File Path**: `Mathlib/NumberTheory/Cyclotomic/Discriminant.lean`

**Relevant Lemmas**:
- `IsCyclotomicExtension.discr_odd_prime`:
  ```lean
  theorem discr_odd_prime [IsCyclotomicExtension {p} K L] [hp : Fact p.Prime]
      (hζ : IsPrimitiveRoot ζ p) (hirr : Irreducible (cyclotomic p K)) (hodd : p ≠ 2) :
      discr K (hζ.powerBasis K).basis = (-1) ^ ((p - 1) / 2) * p ^ (p - 2)
  ```
- **Absolute Discriminant of $\mathbb{Q}(\zeta_p)$**:
  Since $\mathcal{O}_K = \mathbb{Z}[\zeta_p]$, the discriminant of the field `NumberField.discr K` is equal to the discriminant of this power basis.
  You can use `discr_prime_pow` with $k=1$ for $p^1$.

## Q7: Class Number Bounds in Mathlib

Currently, Mathlib **does not** contain a lemma of the form `log(h_K)/f ≤ C * log(rd(K))` (like Brauer-Siegel or explicit Stirling-based Minkowski bounds). Finiteness is proved, and the Minkowski representative exists, but the quantitative counting of ideals up to the Minkowski bound is not yet a named theorem in the library.

To close Gap S2, you will likely need to:
1. Use `exists_ideal_in_class_of_norm_le` to say $h_K \le \# \{ I \mid \text{absNorm } I \le M K \}$.
2. Use the fact that the number of ideals with norm $\le X$ is bounded by a polynomial in $X$ (or similar) to get the logarithmic bound.
3. This derivation will remain a `sorry` until more quantitative ANT results are added to Mathlib.
