# Mathlib v4.30 — Cyclotomic Splitting and Factorization API

This document provides the exact lemma names and signatures for the 4 sorries in `Erdos90/CMField/CyclotomicSplitPrimes.lean`.

## 1. Inertia Degree and Ramification Index

For $K = \mathbb{Q}(\zeta_m)$, the behavior of a prime $q \nmid m$ is determined by the order of $q$ in $(\mathbb{Z}/m\mathbb{Z})^\times$.

**Source**: `Mathlib/NumberTheory/NumberField/Cyclotomic/Ideal.lean`

### `inertiaDeg_eq_one`
- **Lemma**: `IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd`
- **Signature**:
  ```lean
  theorem inertiaDeg_eq_of_not_dvd {p : ℕ} [hp : Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
      [hP : P.IsPrime] [hP_lies : P.LiesOver (span {(p : ℤ)})] (hm : ¬ p ∣ m) :
      inertiaDeg (span {(p : ℤ)}) P = orderOf (p : ZMod m)
  ```
- **Application**: For $m = p$ (the cyclotomic prime) and a prime $q \equiv 1 \pmod p$, we have $q \nmid p$. Then `inertiaDeg = orderOf (q : ZMod p)`. Since $q \equiv 1 \pmod p$, the order is 1.

### `ramificationIdx_eq_one`
- **Lemma**: `IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd`
- **Signature**:
  ```lean
  theorem ramificationIdx_eq_of_not_dvd {p : ℕ} [hp : Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
      [hP : P.IsPrime] [hP_lies : P.LiesOver (span {(p : ℤ)})] (hm : ¬ p ∣ m) :
      ramificationIdx (span {(p : ℤ)}) P = 1
  ```
- **Application**: Since $q \nmid p$, the ramification index is 1.

---

## 2. Number of Primes Over $q$

### `card_primesOver_eq`
- **Lemma**: `ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`
- **Source**: `Mathlib/NumberTheory/RamificationInertia/Basic.lean`
- **Identity**: $g \cdot e \cdot f = [K : \mathbb{Q}]$
- **Calculation**:
  - $[K : \mathbb{Q}] = p-1$ (degree of $\mathbb{Q}(\zeta_p)$).
  - $e = 1$ (by `ramificationIdxIn_eq_of_not_dvd`).
  - $f = 1$ (by `inertiaDegIn_eq_of_not_dvd`).
  - Therefore, $g \cdot 1 \cdot 1 = p-1 \implies g = p-1$.
- **Note**: Use `Finset.card` or `Set.ncard` depending on the local definition.

---

## 3. Complex Conjugation and Ideal Fixing

### `conjIdeal_ne_self`
This lemma requires showing that complex conjugation $\tau$ does not fix a prime $P$ above a completely split $q$.

**Logic**:
1. **Stabilizer is Decomposition Group**: The stabilizer of $P$ under the Galois action is the decomposition group $D_P$.
   - **Mathlib**: `MulAction.stabilizer (K ≃ₐ[ℚ] K) P`.
2. **Cardinality of $D_P$**: In a Galois extension, $|D_P| = e \cdot f$.
   - **Proof**: Since $e=1$ and $f=1$ for $q \equiv 1 \pmod p$, $|D_P| = 1 \cdot 1 = 1$.
   - Thus $D_P = \{1\}$.
3. **Complex Conjugation is Nontrivial**: For $p > 2$, `complexConj K` has order 2.
   - **Lemma**: `IsCMField.complexConj_ne_one` or `orderOf_complexConj = 2`.
4. **Conclusion**: Since $\tau \neq 1$ and $D_P = \{1\}$, we must have $\tau(P) \neq P$.

---

## 4. Class Group and Minkowski API

### Class Group Representative
- **Lemma**: `NumberField.exists_ideal_in_class_of_norm_le`
- **Usage**: Given an ideal class $C$, find an integral ideal $I \in C$ with $N(I) \le \text{MinkowskiBound}$.

### Principal Ideal Check
- **Lemma**: `ClassGroup.mk_eq_one_iff`
- **Usage**: $I$ is principal iff $[I] = 1$ in the class group.

### Mapping Signs to Ideals
- Pick a set of split primes $\{P_1, \dots, P_m\}$.
- For each sign vector $\epsilon \in \{\pm 1\}^m$, define $J_\epsilon = \prod P_j^{(1-\epsilon_j)/2}$ (so $P_j$ is in the product iff $\epsilon_j = -1$).
- Show that these $J_\epsilon$ map to distinct classes or that their ratios are not principal unless signs match.
