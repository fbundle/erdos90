# Mathlib v4.30 — Class Group API and Minkowski Bound

This document details the Mathlib functions and theorems for working with ideal classes and the Minkowski bound, specifically for the `hmk_unit_inj` proof.

## 1. Class Group Basics

- **Definition**: `ClassGroup R` is the group of fractional ideals modulo principal ideals.
- **Mapping Ideals to Classes**: `ClassGroup.mk0 : Ideal R → ClassGroup R` (for integral ideals).
- **Equality in Class Group**:
  ```lean
  ClassGroup.mk0_eq_mk0_iff {I J : (Ideal (𝓞 K))⁰} :
      ClassGroup.mk0 I = ClassGroup.mk0 J ↔
      ∃ x : (𝓞 K)×, (I : Ideal (𝓞 K)) = ↑x • (J : Ideal (𝓞 K))
  ```
- **Principal Ideals**: $I$ is principal if and only if `ClassGroup.mk0 I = 1`.

## 2. Minkowski Bound

- **Theorem**: `NumberField.exists_ideal_in_class_of_norm_le`
- **Signature**:
  ```lean
  theorem exists_ideal_in_class_of_norm_le (C : ClassGroup (𝓞 K)) :
      ∃ I : Ideal (𝓞 K), ClassGroup.mk0 ⟨I, _⟩ = C ∧ Ideal.absNorm I ≤ ⌊M K⌋₊
  ```
- **Context**: Every ideal class has a representative whose absolute norm is bounded by the Minkowski constant $M_K$. This is used to bound the size of the class group or to find small representatives for unit proofs.

## 3. Units and Real Subfields

- **Real Units**: Units that lie in the maximal real subfield $K^+$.
- **Index Theorem**: `NumberField.IsCMField.indexRealUnits_eq_one_or_two`
- **Complex Conjugation on Units**:
  - `IsCMField.unitsMulComplexConjInv (K) : (𝓞 K)ˣ →* torsion K`
  - This map sends $u$ to $u/\bar{u}$, which is always a root of unity in a CM field.
  - The kernel of this map is the set of "real units" (units $u$ such that $u = \bar{u}$).

## 4. Logical Steps for `hmk_unit_inj`

1. **Construct Ideals**: For a sign vector $\epsilon \in \{\pm 1\}^m$, let $J_\epsilon = \prod P_j^{(1-\epsilon_j)/2}$.
2. **Assume Non-injectivity**: Suppose $[J_{\epsilon_1}] = [J_{\epsilon_2}]$.
3. **Obtain Generator**: Then $J_{\epsilon_1} \cdot J_{\epsilon_2}^{-1} = (\alpha)$ for some $\alpha \in K^\times$.
4. **Valuation Analysis**: At a split prime $P_j$, $v_{P_j}(\alpha) = v_{P_j}(J_{\epsilon_1}) - v_{P_j}(J_{\epsilon_2})$.
   - If $\epsilon_{1,j} \neq \epsilon_{2,j}$, then $v_{P_j}(\alpha) \neq 0$.
5. **Contradiction**: Use the fact that if $\alpha/\bar{\alpha}$ is a root of unity (which it is for CM fields), then its valuation at split primes must satisfy certain constraints, or use the fact that these split primes were chosen to be "non-principal" or "independent" in the class group.
6. **Norm Argument**: $\|\alpha\| = 1$ often follows from the construction if $\alpha$ is a unit or related to torsion.
