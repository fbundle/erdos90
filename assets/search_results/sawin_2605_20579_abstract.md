# Source: https://arxiv.org/abs/2605.20579

# arXiv Paper: An Explicit Lower Bound for the Unit Distance Problem

**Title:** "An explicit lower bound for the unit distance problem"

**Author:** Will Sawin

**arXiv Identifier:** 2605.20579

**Submission Date:** May 20, 2026

**Subject Areas:** Combinatorics (math.CO); Metric Geometry (math.MG); Number Theory (math.NT)

## Abstract

The paper demonstrates that sets of n points in a plane can contain "more than n^{1.014} pairs of points separated by a distance exactly 1" for arbitrarily large n values. This work improves upon recent OpenAI research that established a similar result using an inexplicit exponent greater than 1, advancing beyond previous lower bounds and refuting an Erdős conjecture. The approach employs number-theoretic methods, specifically constructing algebraic number fields with particular properties using "a Golod-Shafarevich criterion argument."

## Access Information

The paper is available in multiple formats:
- PDF version
- HTML (experimental)
- TeX Source

**DOI:** https://doi.org/10.48550/arXiv.2605.20579

The submission was made by Will Sawin on May 20, 2026, with a file size of 17 KB.

---

## Extended Content (from HTML version)

## Main Contribution

Will Sawin proves that sets of n points in the plane can contain more than n^1.014 pairs separated by exactly unit distance, improving recent work by OpenAI researchers who established a lower bound with an unspecified exponent greater than 1.

## Key Results

**Theorem 1** establishes the existence of n-point sets U in ℝ² with at least n^1.014114/C unit distance pairs, where C is an absolute constant.

## Context

- **Previous bounds**: Erdős achieved n^(1 + c/log log n) and conjectured this was optimal
- **Upper bound**: Spencer, Szemerédi, and Trotter proved O(n^4/3)
- **Recent breakthrough**: OpenAI team (Chen, Sellke, Sawhney) disproved Erdős's conjecture with δ > 0 unspecified

## Methodology

The proof uses **algebraic number theory**, constructing:

1. **CM fields** (complex multiplication) with:
   - Totally real subfields F
   - Totally imaginary quadratic extensions K

2. **Golod-Shafarevich criterion** to produce 2-class field towers with:
   - Growing degree
   - Small discriminant
   - Many small-norm primes

3. **Lattice projections** where short lattice vectors project to unit-distance pairs in ℝ²

## Technical Improvements Over OpenAI Approach

- Uses fractional ideals instead of rings of integers
- Employs relative class numbers (smaller than absolute class numbers)
- Works with non-split primes (primes not split in field extensions)
- Optimizes the pigeonhole argument via class group quotienting
- Tightens bounds using Louboutin's explicit relative class number estimates

## Parameter Selection

The proof uses:
- T = {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43}
- S_ℚ = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 47, 71, 79, 97, 101, 107, 109, 139, 151, 163, 167, 179}
- R = 72, with carefully chosen k(p) values

## Significance

This represents substantial progress toward understanding the true exponent, closing the gap between the lower bound (1.014) and upper bound (1.333 ≈ 4/3). Future improvements likely require analytic number theory or computational optimization of parameters.
