# Mathlib has Hermite–Minkowski (partial)

## Finding

`Mathlib/NumberTheory/NumberField/Discriminant/Basic.lean:496`:

```lean
theorem _root_.NumberField.finite_of_discr_bdd :
    {K : { F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
      haveI :  NumberField K := @NumberField.mk _ _ inferInstance K.prop
      |discr K| ≤ N }.Finite
```

**Status**: Fully proved in Mathlib v4.30 (no sorry).

**Subset**: Among number fields embedded in a fixed algebraic closure `A`,
there are finitely many with `|discr K| ≤ N`.

## What this could provide

Hermite–Minkowski opens a tractable Mathlib path for **uniform lower bounds**
on the regulator over bounded-discriminant number fields:

1. Take `A = ℚ̄` (algebraic closure of `ℚ`).
2. Apply `finite_of_discr_bdd` to get finitely many K with `|discr K| ≤ N`.
3. For each, `Units.regulator_pos K : 0 < regulator K`.
4. Take minimum over finite set: `R_min(N) := min { regulator K | |discr K| ≤ N } > 0`.

This gives a **uniform regulator bound** that doesn't require Friedman 1989's
analytic continuation argument.

## Caveat: degree growth in BRD towers

In the HMR BRD tower used by Erd46, `rootDiscr K_n` stays bounded but
`[K_n : ℚ]` grows.  Since `|disc K| = (rootDiscr K)^[K:ℚ]`, bounded
`rootDiscr` does NOT imply bounded `|disc K|`.  So `finite_of_discr_bdd`
gives finitely many K with bounded *disc*, but our tower has K with bounded
*rootDiscr* (which is different).

**Consequence**: a uniform `R_min(rd_F)` via HM doesn't work for the BRD
tower — we have infinitely many tower levels, each with rootDiscr ≤ rd_F
but disc growing.  The naive HM approach fails.

## Friedman's bound is genuinely needed

Friedman 1989's `R_K ≥ 0.2052` is uniform over ALL number fields,
regardless of degree.  This uniformity is what HM cannot replicate.

The proof of Friedman uses:
- Hadamard inequality on the unit lattice (Mathlib: lattice covolume framework exists).
- Mahler measure bounds on units (Smyth 1971 for non-reciprocal; Dobrowolski 1979 unconditional).
- Mellin transform manipulations (not in Mathlib).

## Alternative angles

1. **Use Smyth's theorem directly**: for any unit u with [K(u):ℚ] = m and u not
   reciprocal, the height of u is ≥ log(θ_0)/(2m) where θ_0 ≈ 1.3247... (the
   real root of x³ = x + 1).  This is in `assets/anick_dicks_gs.pdf` lemma 1.1
   (cited for Anick–Dicks GS argument).  Not in Mathlib.

2. **Use Dobrowolski's bound**: for any unit u not a root of unity in K of
   degree d, height(u) ≥ (1/d)·(log log d / log d)^3.  Unconditional but weaker.
   Not in Mathlib.

3. **Use the proved E13 regulator inequality**: PER `class_num_bound_of_brd`,
   if we could replace the `regulator K ≥ 1/8` with an explicit weak bound
   like `regulator K ≥ exp(-f)` (i.e., the chain becomes `log(h_K)/f ≤ 2 log(2 rd_F) + O(1)`),
   the asymptotic claim still holds.  But the proof currently uses 1/8 in a
   tight constant manipulation; a weaker bound changes the exact constant.

## Conclusion

Hermite–Minkowski is in Mathlib but doesn't replace Friedman 1989 for our
context.  The genuine remaining Mathlib gap is the L-function tooling
underlying Friedman's bound.

Document for future contributor: don't waste time trying to use HM for
`regulator_lower_bound_cm`; the degree-growth in the BRD tower defeats the
finite-intersection approach.
