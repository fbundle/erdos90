# Galois Action on Ideals and Decomposition Groups in Mathlib 4

This document provides the technical bridge between the Galois group action on ideals and the decomposition group, specifically for proving that complex conjugation does not fix a completely split prime.

## 1. Action of Galois Group on Ideals

In Mathlib, the Galois group `G = (L ≃ₐ[K] L)` acts on the ring of integers `B = 𝓞 L`. This action extends to the set of ideals `Ideal B`.

- **Action Definition**: `MulAction G (Ideal B)`
- **Lemma**: `Ideal.map σ P` (where `σ : G`) is the action of `σ` on ideal `P`.
- **Transitivity**: If `P1` and `P2` are prime ideals lying over the same prime `p` of `A`, there exists `σ ∈ G` such that `Ideal.map σ P1 = P2`.
  - **Lemma**: `Algebra.IsInvariant.exists_smul_of_under_eq` (or similar in `Mathlib/RingTheory/Invariant/Basic.lean`).

## 2. The Decomposition Group as a Stabilizer

The **decomposition group** $D_P$ of a prime ideal $P$ is the subgroup of elements in $G$ that fix $P$.

- **Definition**: `MulAction.stabilizer G P`
- **Cardinality Theorem**: For a Galois extension $L/K$ and prime $P$ over $p$:
  $$|G| = g \cdot e \cdot f$$
  where $g$ is the number of primes over $p$, $e$ is the ramification index, and $f$ is the inertia degree.
- **Decomposition Group Order**: $|D_P| = e \cdot f$.
  - **Proof Path**: Since $G$ acts transitively on the $g$ primes over $p$, the orbit-stabilizer theorem gives $|G| = |Orbit(P)| \cdot |Stabilizer(P)| = g \cdot |D_P|$. Comparing with $|G| = g \cdot e \cdot f$ yields $|D_P| = e \cdot f$.

## 3. The Totally Split Case

A prime $p$ **splits completely** if $e=1$ and $f=1$.
- **Implication**: $|D_P| = 1 \cdot 1 = 1$.
- **Consequence**: $D_P$ is the trivial subgroup $\{1\}$.
- **Fixing Property**: $\sigma(P) = P \iff \sigma = 1$.

## 4. Complex Conjugation in Cyclotomic Fields

For $K = \mathbb{Q}(\zeta_p)$ ($p > 2$):
- **Automorphism**: `IsCMField.complexConj K` (or `zeta_p \mapsto zeta_p^{-1}`).
- **Order**: The order of complex conjugation is 2.
- **Nontriviality**: `complexConj K ≠ 1` because $p > 2$ implies $\mathbb{Q}(\zeta_p)$ is not a real field.
- **Action on Split Primes**: If $q \equiv 1 \pmod p$, then $q$ splits completely in $K$. Any prime $P$ over $q$ has a trivial decomposition group. Since `complexConj` is not the identity, it cannot fix $P$.
- **Result**: `conjIdeal K P ≠ P`.

## 5. Mathlib Lemma Summary

| Concept | Mathlib Name / Path |
| :--- | :--- |
| **Galois Action** | `MulAction (L ≃ₐ[K] L) (Ideal (𝓞 L))` |
| **Stabilizer** | `MulAction.stabilizer` |
| **Transitivity** | `Ideal.is_galois.transitive_action` |
| **Index Relation** | `ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn` |
| **Complex Conj** | `IsCMField.complexConj` |
| **Nontriviality** | `IsCMField.complexConj_ne_one` |
