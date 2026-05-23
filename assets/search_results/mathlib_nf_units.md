# Source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/Units/Basic.html

# Mathlib.NumberTheory.NumberField.Units.Basic

This documentation covers the fundamental properties of units in the ring of integers of a number field and their torsion subgroup.

## Core Topic

The module examines the group `(𝓞 K)ˣ` of units in the ring of integers `𝓞 K` for a number field `K`, with particular focus on torsion elements.

## Main Definition

**Torsion Subgroup**: The module defines `NumberField.Units.torsion`, which represents the torsion subgroup of the unit group.

## Key Theorems

**Unit Characterization**: An element `x : 𝓞 K` qualifies as a unit if and only if the absolute value of its norm over ℚ equals 1.

**Torsion Membership**: A unit belongs to the torsion subgroup precisely when it evaluates to 1 under every infinite place of the number field.

**Torsion Properties**:
- The torsion subgroup is finite
- It forms a cyclic group
- Its cardinality is always even
- When the field has odd finrank over ℚ, the torsion subgroup contains only ±1

**Root Unity Connection**: The roots of unity of order dividing the torsion order exactly comprise the torsion subgroup.

## Supporting Results

The module provides coercion lemmas establishing that units embed into the field, along with theorems about complex embeddings and norm preservation under unit operations.
