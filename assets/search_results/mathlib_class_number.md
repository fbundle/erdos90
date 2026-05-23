# Source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/ClassNumber.html

# Mathlib.NumberTheory.NumberField.ClassNumber Documentation

## Overview
This Lean 4 module defines and studies the class number of number fields, representing the cardinality of the class group of a number field's ring of integers.

## Main Definition

**Class Number**: The class number of a number field K equals `Fintype.card (ClassGroup (RingOfIntegers K))`. This measures the failure of unique factorization in the ring of integers.

## Key Theorems

**Finiteness Properties**:
- The class group is always finite (via `instFintypeClassGroup`)
- `classNumber_ne_zero`: Class number is always nonzero
- `classNumber_pos`: Class number is always positive

**Characterization**: "The class number of a number field is `1` iff the ring of integers is a PID."

**Minkowski Bound Application**: The module establishes that every ideal class contains an ideal with norm at most the Minkowski bound `M(K) = (4/π)^r₂ · (n! / n^n) · √|disc(K)|`, where n is the degree and r₂ counts complex embeddings.

**`exists_ideal_in_class_of_norm_le`** (in `ClassNumber.lean`): Every ideal class has a representative with norm ≤ Minkowski bound.

## Principality Criteria

Three theorems provide practical methods for proving `RingOfIntegers K` is principal:

1. **General criterion**: If all ideals with norm ≤ M(K) are principal
2. **Prime-specific criterion**: If only prime ideals with norm ≤ M(K) are principal
3. **Galois case**: For Galois extensions, checking finitely many primes p ∈ [1, ⌊M(K)⌋₊]

## Special Cases

**Discriminant Bound**: If |disc(K)| < (2π/4)^r₂ · (n^n/n!), then the ring of integers is a PID.

**Rationals**: "The class number of ℚ equals 1", reflecting that ℤ is a PID.
