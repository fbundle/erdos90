import Erdos90.Arithmetic
import Erdos90.Geometric
import Erdos90.Main

/-!
# Axioms (for human verification)

This file collects every postulate that the proof assumes without
a formal Lean derivation.  Each corresponds to a deep theorem in the
literature or a substantial computation.

**All axioms should be reviewed by a number theorist / geometer.**

The axioms are declared in the modules that need them:
- `Arithmetic.lean`: Axiom 1 (`exists_admissible_family`)
- `Geometric.lean`: Axiom 2 (`exists_good_coset`)
-/

open Real

noncomputable section

/-!
## Axiom 1: Existence of the admissible tower (Proposition 3.8 of the paper)

**Location**: `Erdos90/Arithmetic.lean`, declared as `axiom exists_admissible_family`.

**Statement**: There exist absolute constants γ > 0 and D > 0 such that,
for arbitrarily large f, there is an admissible family with those γ and D.

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
-/

#check exists_admissible_family

/-!
## Axiom 2: Coset averaging (Lemma 2.4)

**Location**: `Erdos90/Geometric.lean`, declared as `axiom exists_good_coset`.

Using Haar probability measure on the torus ℂ^f/Λ, the expected size
of (a+Λ) ∩ B_R is vol(B_R)/covol(Λ), and the expected number of ordered
U-pairs (x, x+u) with u ∈ U is |U|·a(R)^f / covol(Λ).

**Statement**: For an admissible family A and radius R > 1/2 with
log ρ(R) > -γ/2, there exists a coset a+Λ such that the finite
intersection X = (a+Λ) ∩ B_R is nonempty and satisfies the counting
estimate E ≥ e^{γf/2}·|X|, where E counts ordered pairs (x, y) ∈ X²
with y-x ∈ U.

**Verification**: Standard Fubini/averaging argument on the compact abelian
group ℂ^f/Λ.  The lattice Λ is discrete and cocompact; Haar probability
measure μ on the quotient satisfies:
- ∫ N(a+Λ) dμ(a) = vol(B_R) / covol(Λ)  (by Fubini on a fundamental domain)
- ∫ E(a+Λ) dμ(a) = |U| · a(R)^f / covol(Λ)  (overlap area for U-pairs)
From log ρ(R) > -γ/2 we have a(R)^f > (πR²)^f · exp(-γf/2), and |U| ≥ exp(γf).
Hence ∫ E ≥ exp(γf/2) · ∫ N, so some coset achieves the average.

**Status**: Declared as `axiom`; the Lean proof requires `IsAddFundamentalDomain`
measure-theoretic API that is not yet fully exercised in this project.
-/

#check exists_good_coset

/-!
## Proven statements (formerly axioms)

The following statements are now **fully proven** in Lean:

### `exists_R_log_rho_gt` (formerly Axiom 2)
**Location**: `Erdos90/Geometric.lean`, lemma.

Existence of R > 1/2 with log ρ(R) > -ε and 4RD > 1.
Proved via `tendsto_rho_atTop`: ρ(R) → 1 as R → ∞, so eventually
ρ(R) > exp(-ε) and log ρ(R) > -ε.

### `size_bound` (formerly Axiom 4)
**Location**: `Erdos90/Geometric.lean`, lemma.

In the sup-norm polydisc, |X| ≤ exp(2f·log(4RD+1)).
Proved via grid discretization: first-coordinate projection to a
(2D)⁻¹-grid with M = ⌊4RD⌋+1 cells per coordinate.

### `first_coordinate_separation` (formerly Axiom 5)
**Location**: `Erdos90/Geometric.lean`, lemma.

For nonzero v ∈ Λ, ‖v(fin0 A.hf)‖ ≥ D⁻¹.
Proved directly from the `hΛ_sep` field of `AdmissibleFamily`
(after strengthening the structure field to use `fin0 hf`).

---

## Remaining axioms (awaiting human verification)

1. **`exists_admissible_family`** (`Arithmetic.lean`) — Golod-Shafarevich tower
2. **`exists_good_coset`** (`Geometric.lean`) — Haar measure coset averaging

All other lemmas and theorems are fully proven, including:
- `projection_injective` (Lemma 2.5)
- `card_ordered_unit_pairs_eq_two_mul_unitDistPairs` (counting identity)
- `size_bound` (Axiom 4) — grid discretization proof
- `planar_set_from_datum` (Theorem 2.3 parametric form)
- `admissible_family_to_planar_set` (Theorem 2.3)
- `erdos_unit_distance_false` (Theorem 1.1)
- `erdos_bound_false` (contrapositive of Theorem 1.1)
- `tendsto_rho_atTop` — ρ(R) → 1 as R → ∞
- `rho_formula` — algebraic simplification of ρ(R)
- `first_coordinate_separation` — first-coordinate separation bound
- `exists_R_log_rho_gt` — existence of suitable R
-/

#check admissible_family_to_planar_set
#check erdos_unit_distance_false
#check erdos_bound_false
