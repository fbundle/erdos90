import Erdos90.Arithmetic
import Erdos90.Geometric
import Erdos90.Main

/-!
# Axioms (for human verification)

This file collects every postulate that the proof assumes without
a formal Lean derivation.  Each corresponds to a deep theorem in the
literature or a substantial computation.

**All axioms should be reviewed by a number theorist / geometer.**

There is now a single remaining axiom:
- `exists_admissible_family` (`Arithmetic.lean`): encapsulates both
  the Golod–Shafarevich tower construction (Proposition 3.8) and the
  Haar measure coset averaging (Lemma 2.4), via the `h_coset_avg` field
  of `AdmissibleFamily`.
-/

open Real

noncomputable section

/-!
## Axiom 1: Existence of the admissible tower with coset averaging
   (Proposition 3.8 + Lemma 2.4 of the paper)

**Location**: `Erdos90/Arithmetic.lean`, declared as `axiom exists_admissible_family`.

**Statement**: There exist absolute constants γ > 0 and D > 0 such that,
for arbitrarily large f, there is an admissible family with those γ and D.

The `AdmissibleFamily` structure packages both the tower construction output
and the coset averaging property:

### Tower construction (Proposition 3.8)

In the paper, D is the denominator of the base CM field and is fixed
for the entire tower.  γ = t·log 2 - log H where t is the number of
split primes and H is the class-number bound.

**Mathematical input**:
- Proposition 3.2: Cyclotomic base field F (cyclic cubic, totally real)
- Proposition 3.4: Golod–Shafarevich inequality (r > d²/4 ⇒ infinite pro-p group)
- Proposition 3.5: Shafarevich relation-rank estimate (r(G) ≤ d(G) + C₀)
- Proposition 3.6: Chebotarev density theorem (split primes with trivial Frobenius)
- Proposition 3.7: Minkowski ideal-class bound (h(K) ≤ rd(K)^{O([K:ℚ])})
- Proposition 2.2: Class-group pigeonhole (|U| ≥ e^{(t log 2 - log H)f})

### Coset averaging (Lemma 2.4, `h_coset_avg` field)

Using Haar probability measure on the torus ℂ^f/Λ, the expected size
of (a+Λ) ∩ B_R is vol(B_R)/covol(Λ), and the expected number of ordered
U-pairs (x, x+u) with u ∈ U is |U|·a(R)^f / covol(Λ).

For an admissible family A and radius R > 1/2 with log ρ(R) > -γ/2,
there exists a coset a+Λ such that the finite intersection X = (a+Λ) ∩ B_R
is nonempty and satisfies E ≥ e^{γf/2}·|X|, where E counts ordered pairs
(x, y) ∈ X² with y-x ∈ U.

**Verification**: Standard Fubini/averaging argument on the compact abelian
group ℂ^f/Λ.  The lattice Λ is discrete and cocompact; Haar probability
measure μ on the quotient satisfies:
- ∫ N(a+Λ) dμ(a) = vol(B_R) / covol(Λ)  (by Fubini on a fundamental domain)
- ∫ E(a+Λ) dμ(a) = |U| · a(R)^f / covol(Λ)  (overlap area for U-pairs)
From log ρ(R) > -γ/2 we have a(R)^f > (πR²)^f · exp(-γf/2), and |U| ≥ exp(γf).
Hence ∫ E ≥ exp(γf/2) · ∫ N, so some coset achieves the average.

**Status**: The `h_coset_avg` field is part of `AdmissibleFamily` and is
subsumed by `exists_admissible_family`.  A full Lean proof would require
`IsAddFundamentalDomain` measure-theoretic API not yet exercised here.
-/

#check exists_admissible_family
