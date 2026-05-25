# Gap S1: Valuation Arithmetic and Q²-Scaling

## Q1: `mem_integers_of_valuation_le_one`

**File Path**: `Mathlib/RingTheory/DedekindDomain/AdicValuation.lean`

**Lemma Statement**:
```lean
theorem mem_integers_of_valuation_le_one (x : K)
    (h : ∀ v : HeightOneSpectrum R, v.valuation K x ≤ 1) : x ∈ (algebraMap R K).range
```

**Usage & Conversion**:
- `HeightOneSpectrum.valuation K x` returns a value in `ℤᵐ⁰` (which is `WithZero (Multiplicative ℤ)`).
- The inequality `v.valuation K x ≤ 1` uses multiplicative notation. In additive notation, this is equivalent to $v_P(x) \ge 0$.
- To convert `∀ v, v.valuation K x ≤ 1` into the result, you just need to provide the hypothesis for all prime ideals (height one spectrum).

## Q2: `Ideal.absNorm` API

**File Path**: `Mathlib/RingTheory/Ideal/Norm/AbsNorm.lean`

**Relevant Lemmas**:
- `map_mul Ideal.absNorm`: `absNorm (I * J) = absNorm I * absNorm J`.
- `Ideal.absNorm_span_singleton (r : S) : absNorm (span {r}) = (Algebra.norm ℤ r).natAbs`.
- `Ideal.absNorm_eq_pow_inertiaDeg`: (in `Mathlib/NumberTheory/RamificationInertia/Inertia.lean`)
  ```lean
  lemma absNorm_eq_pow_inertiaDeg [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] {p : ℤ}
      (P : Ideal R) (hp : Prime p) [P.IsMaximal] (hL : P.LiesOver (span {p})) :
      absNorm P = p.natAbs ^ inertiaDeg (span {p}) P
  ```
- **Rational Prime Below**: Use `Ideal.under ℤ P` to get the ideal $(q) = P \cap \mathbb{Z}$.
  - `Nat.absNorm_under_prime`: If `P` is prime, then `absNorm (under ℤ P)` is a prime number.

## Q3: Prime Splitting

- **Splitting**: For split primes in a Galois CM extension $K/F$, if $q \mathcal{O}_F = \mathfrak{p}$ is a prime that splits as $\mathfrak{p}\mathcal{O}_K = P \bar{P}$, then:
  - `(q : 𝓞 K) = P * conjIdeal K P` (where `conjIdeal` is complex conjugation).
  - `absNorm P = q` (if the inertia degree is 1, which is true for split primes in the GS tower construction).

## Q4: `FractionalIdeal.count` API

**File Path**: `Mathlib/RingTheory/DedekindDomain/Factorization.lean`

**Relevant Lemmas**:
- `count_mul (hI : I ≠ 0) (hI' : I' ≠ 0) : count K v (I * I') = count K v I + count K v I'`.
- `count_self : count K v (v.asIdeal : FractionalIdeal R⁰ K) = 1`.
- `count_spanSingleton`: There isn't a single direct lemma, but it can be derived using `count_well_defined`. For $x \in R \setminus \{0\}$, `count K v (spanSingleton R⁰ (algebraMap R K x)) = (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {x})).factors`.
- **Additive Valuation**: `FractionalIdeal.count` **IS** the additive valuation $v_P(I)$. The documentation says: `FractionalIdeal.count K v I` (abbreviated as `val_v(I)`) is $n_v$ in $I = \prod v^{n_v}$.
- **Formula for Principal Ideal**: For $x = a/b \in K^\times$, `count K v (spanSingleton R⁰ x) = val_v(a) - val_v(b)`.
