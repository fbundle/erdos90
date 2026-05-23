# Source: https://arxiv.org/pdf/2605.20579

# An explicit lower bound for the unit distance problem

**Author:** Will Sawin
**arXiv:** 2605.20579
**Date:** May 20, 2026

NOTE: The PDF was fetched but returned as binary content (418.9KB). The WebFetch tool could not decode the compressed PDF streams. The following is the best available extracted content from the HTML version.

---

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

## Document Structure (from PDF metadata)

The paper contains:
- Multiple theorems (theo.1 through theo.15)
- Several equations (equation.1 through equation.12)
- References section
- Discussion and proofs sections across 15 pages
- File size: 17 KB (TeX source), 418.9 KB (PDF)
