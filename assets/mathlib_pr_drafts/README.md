# Mathlib PR drafts

This directory contains **standalone Lean files** extracted from the Erd46
formalization that are ready (with minimal cleanup) for submission as
individual Mathlib PRs.

Each file has:
- Proper Mathlib copyright header
- Explicit imports (only what's needed)
- Mathlib-style docstrings
- Proper namespace structure

## Drafts

### `Nat_TotientReverse.lean` — `Nat.le_four_mul_totient_sq`

**Target Mathlib location:** `Mathlib/Data/Nat/Totient.lean`

**Statement:** For any `n : ℕ`, `n ≤ 4 · (Nat.totient n)²`.

**Proof:** Strong induction via `Nat.recOnPosPrimePosCoprime` for the odd
helper, then 2-adic decomposition for general n.

**Lines:** ~120.

**Status:** Fully proved in our codebase (`Erdos90/Mathlib4_Extra/ClassNumberBound.lean`)
and replicated here in standalone form.

### `NumberField_ClassNumberFormula.lean` — `classNumber_eq_residue_formula`

**Target Mathlib location:** `Mathlib/NumberTheory/NumberField/DedekindZeta.lean`

**Statement:** The Dirichlet class number formula in algebraic-identity form,
solving Mathlib's existing `dedekindZeta_residue_def` for `classNumber K`.

**Proof:** Pure algebraic rearrangement via `field_simp`.

**Lines:** ~30.

**Status:** Fully proved.

### `NumberField_TorsionOrderBridge.lean` — `totient_torsionOrder_le_finrank`

**Target Mathlib location:** `Mathlib/NumberTheory/NumberField/Units/Basic.lean`
or `Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean`.

**Statement:** For a number field K, `(torsionOrder K).totient ≤ [K:ℚ]`.

**Proof:** Extract a primitive root from the cyclic torsion subgroup, lift
to K, apply `IsPrimitiveRoot.lcm_totient_le_finrank`.

**Lines:** ~25.

**Status:** Fully proved.

## How to use these drafts

To submit any of these as a Mathlib PR:
1. Copy the `.lean` file content
2. Adjust the author line as needed (mathlib uses `Authors:` for individual
   contributors; the original work is already credited via the Erd46 commit
   history)
3. Place at the target Mathlib location
4. Update the namespace if Mathlib's organization differs
5. Verify imports are minimal
6. Submit as a Mathlib PR with reference to this project

## Why these are useful for Mathlib

Each lemma fills a small gap in Mathlib's existing infrastructure:
- `Nat.le_four_mul_totient_sq` complements the existing `Nat.totient_le`
- `classNumber_eq_residue_formula` provides the "solved-for-h_K" form that
  applications typically need
- `totient_torsionOrder_le_finrank` is a standard Mathlib-shaped bridge
  that bridges the torsion order with the field degree

None of these depend on the deeper Mathlib gaps (class field theory,
L-function functional equations, etc.) that the Erd46 project's load-bearing
sorries require.
