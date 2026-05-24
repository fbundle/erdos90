# Cyclotomic Proof Documentation

## 1. Cyclotomic Prime Splitting Lemmas (Mathlib/NumberTheory/NumberField/Cyclotomic/Ideal.lean)
- `inertiaDeg_eq_of_not_dvd` (or `inertiaDegIn_eq_of_not_dvd`): If $p \nmid m$, then the inertia degree is the order of $p$ in $(\mathbb{Z}/m\mathbb{Z})^\times$.
- `ramificationIdx_eq_of_not_dvd`: If $p \nmid m$, then the ramification index is 1.

## 2. Fundamental Relation
- `sum_ramification_inertia` (Fundamental Equation): $\sum_{\mathfrak{P}|q} e_{\mathfrak{P}} f_{\mathfrak{P}} = [K : \mathbb{Q}]$.
- For $K = \mathbb{Q}(\zeta_p)$ and $q \equiv 1 \pmod p$, $f = 1$ and $e = 1$, so the number of primes above $q$ is $p-1$.

## 3. Class Group & Conjugation
- `ClassGroup.mk_eq_mk`: $I \sim J \iff \exists \alpha \in K^\times, I = (\alpha)J$.
- `NumberField.exists_ideal_in_class_of_norm_le`: Provides representatives bounded by the Minkowski constant.

## 4. Galois Action
- `IsCyclotomicExtension.galoisAction_apply`: Interaction between Galois elements and field elements.
- `conjIdeal_ne_self`: Complex conjugation $\tau$ (sending $\zeta_p \to \zeta_p^{-1}$) is a non-trivial automorphism that doesn't fix split primes above $q \equiv 1 \pmod p$.
