# Source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/ClassGroup.html

# Mathlib.RingTheory.ClassGroup Documentation

## Overview

This Lean 4 module defines the ideal class group for commutative rings, specifically for fractional ideals within a ring's field of fractions.

## Key Definitions

**ClassGroup R**: The quotient of invertible fractional ideals modulo principal ideals, forming a commutative group structure.

**toPrincipalIdeal**: Maps invertible elements `x : K` to the fractional ideal they generate, providing a homomorphism from units of the field of fractions to invertible fractional ideals.

**ClassGroup.mk0**: Sends nonzero integral ideals in Dedekind domains to their corresponding classes in the ideal class group.

**FractionalIdeal.mk0**: Converts nonzero integral ideals into invertible fractional ideals via a monoid homomorphism.

## Main Results

The documentation establishes several critical equivalences:

- `ClassGroup.mk0_eq_mk0_iff` demonstrates that two ideal classes are equal iff there exist nonzero ring elements `x` and `y` satisfying `⟨x⟩ · I = ⟨y⟩ · J`.

- `card_classGroup_eq_one_iff` proves the class number equals one precisely when the ring is a principal ideal domain.

- Ring isomorphisms induce multiplicative equivalences on class groups via `ClassGroup.mulEquiv`.

## Implementation Notes

The definition's independence from the choice of fraction field is established through `ClassGroup.equiv`, ensuring the API remains consistent regardless of which field of fractions is selected for computation.
