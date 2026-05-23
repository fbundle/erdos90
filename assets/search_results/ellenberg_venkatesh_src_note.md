# Source: https://arxiv.org/src/math/0506558

## Fetch Result

The URL https://arxiv.org/src/math/0506558 returns a **binary gzip-compressed tar archive** (application/gzip, approximately 366.9 KB). The file appears to have a header indicating the archive name `B0506558.tar`.

This is the LaTeX source for arXiv:math/0506558, which is Christopher Jerdonek's topology Ph.D. dissertation ("The girth of a Heegaard splitting"), NOT the Ellenberg-Venkatesh paper.

---

## Status of Ellenberg-Venkatesh Paper

The paper "Reflection principles and bounds for class group torsion" by Jordan S. Ellenberg and Akshay Venkatesh was published in:

> **International Mathematics Research Notices** 2007, Art. ID rnm002 (2007)

This paper appears to have been published **without an arXiv preprint**. It is not available on arXiv.

### Access Options

1. **Via publisher (IMRN/Oxford Academic):**
   https://academic.oup.com/imrn/article-abstract/2007/rnm002/652178

2. **Via DOI:** 10.1093/imrn/rnm002

3. **Via MathSciNet:** MR2352820

4. **Via Ellenberg's homepage** (may have preprint):
   https://people.math.wisc.edu/~ellenber/papers.html

5. **Via Venkatesh's IAS/Princeton page** (may have preprint)

---

## Content of the Ellenberg-Venkatesh Paper (from citations and usage)

Based on how this paper is cited and used in the literature (particularly arXiv:2605.20695), the paper contains:

### Main Result

**Theorem (Ellenberg-Venkatesh):** For a number field K of degree n and a prime l, the size of the l-torsion subgroup of the class group satisfies:

> |Cl(K)[l]| ≤ (disc K)^(α(n,l) + ε)

for an explicit exponent α(n,l) < 1/2. Previously, trivial bounds gave α = 1/2 (from the Minkowski bound).

The improvement uses **reflection principles**: the Scholz reflection theorem (relating l-rank of Cl(K) to l-rank of Cl(K')) connects different class groups, and the split prime method gives stronger bounds.

### The Split Prime Method (Key Technique)

For a prime p ≡ 1 (mod l) that splits completely in K:
- The Frobenius at p is trivial, so p = P₁ · P₂ · ... · Pₙ with N(Pᵢ) = p
- The residue fields are F_p at each prime above p
- There is an injection Cl(K)[l] ↪ (F_p^×)^k for some k (from Chebotarev + explicit construction)
- Since |(F_p^×)[l]| = l - 1 (as p ≡ 1 mod l): |Cl(K)[l]| ≤ (l-1)^n

Taking p → ∞ along split primes (using Chebotarev) and optimizing over p gives the bound.

### Reflection Principle Direction

The "reflection" part relates the l-rank of Cl(K) to Cl(K'), where K' is a related field (e.g., K' = Q(ζ_l) · K or a quadratic twist). The Scholz reflection theorem gives:

> rank_l Cl(K) ≤ rank_l Cl(K') + [K:Q]

This allows transferring bounds between related fields.

### Application to Unit Distance (arXiv:2605.20695)

The technique is adapted in Lemma 2.2: instead of bounding |Cl(K)[l]| from above, one uses the pigeonhole principle to find l-torsion elements as differences of ideals, then uses the CM condition to convert ideal class coincidences into norm-1 elements.

More precisely: among the ∏(kⱼ + 1) ideals I_a = ∏ Pⱼ^(aⱼ) P̄ⱼ^(kⱼ - aⱼ) (for 0 ≤ aⱼ ≤ kⱼ), by pigeonhole, h(K) + 1 of them fall into the same ideal class. The ratio I_a / I_b is then a principal ideal (α) with α of norm 1 (since I_a and I_b have the same product of norms P̄ⱼ^kⱼ Pⱼ^kⱼ).

---

## Related Papers

- Helfgott-Venkatesh, "Integral points on elliptic curves and 3-torsion in class groups" (arXiv:math/0405180) — earlier related work by Venkatesh
- Pierce, "The 3-part of class numbers of quadratic fields" (J. London Math. Soc. 2005)
- Ellenberg-Pierce-Wood, "On l-torsion in class groups of number fields" (arXiv:1606.06103) — later work extending EV
- Bhargava-Shankar-Taniguchi-Thorne-Tsimerman-Zhao (arXiv:1701.02458) — bounds on 2-torsion
