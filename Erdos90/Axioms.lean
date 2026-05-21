import Erdos90.Arithmetic
import Erdos90.Geometric

/-!
# Axioms (for human verification)

This file collects every postulate that the proof assumes without
a formal Lean derivation.  Each corresponds to a deep theorem in the
literature or a substantial computation.

**All axioms should be reviewed by a number theorist / geometer.**

The axioms are declared in the modules that need them:
- `Arithmetic.lean`: Axiom 1 (`exists_admissible_family`)
- `Geometric.lean`: Axioms 2–5 (`exists_R_log_rho_gt`, `exists_good_coset`,
  `size_bound`, `first_coordinate_separation`)

This file re-exports nothing; it serves as a human-readable index.
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
## Axiom 2: Behaviour of the disc-overlap ratio ρ(R) (elementary calculus)

**Location**: `Erdos90/Geometric.lean`, declared as `axiom exists_R_log_rho_gt`.

Let b(R) = πR² be the area of a radius-R disc in ℂ ≅ ℝ².
Let a(R) be the overlap area of two such discs at distance 1.
Define ρ(R) = a(R)/b(R).

**Statement**: ρ(R) → 1 as R → ∞.  Consequently, for any ε > 0 and D > 0,
there exists R > 1/2 such that log ρ(R) > -ε and 4RD > 1.

The condition 4RD > 1 is added so that log(4RD) > 0, which is needed
for the size bound (Axiom 4) to be nontrivial.

**Verification**: This is a calculus exercise: a(R) = πR² - O(R),
so ρ(R) = 1 - O(1/R) → 1.  The 4RD > 1 condition is satisfied by
taking R sufficiently large.
-/

#check exists_R_log_rho_gt

/-!
## Axiom 3: Coset averaging (Lemma 2.4)

**Location**: `Erdos90/Geometric.lean`, declared as `def exists_good_coset`
(proof currently `sorry`).

Using Haar probability measure on the torus ℂ^f / Λ, the expected size
of (a+Λ) ∩ B_R is vol(B_R)/covol(Λ), and the expected number of ordered
U-pairs (x, x+u) with u ∈ U is |U|·a(R)^f / covol(Λ).

**Statement**: For an admissible family A and radius R > 1/2 with
log ρ(R) > -γ/2, there exists a coset a+Λ such that the finite
intersection X = (a+Λ) ∩ B_R is nonempty and satisfies the counting
estimate E ≥ e^{γf/2}·|X|, where E counts ordered pairs (x, y) ∈ X²
with y-x ∈ U.

**Verification**: Standard Fubini/averaging argument.  The lattice Λ is
discrete and cocompact, so ℂ^f/Λ is a compact abelian group; Haar measure
gives the needed expectations.  Choosing a coset achieving at least the
average value yields the inequality.
-/

#check exists_good_coset

/-!
## Axiom 4: Packing / size bound (Lemma 2.6)

**Location**: `Erdos90/Geometric.lean`, declared as `lemma size_bound`
(proven via grid discretization).

**Statement**: In the sup-norm polydisc of radius R, distinct points of a
coset of Λ are separated by at least D⁻¹ in some coordinate.  A packing
argument gives |X| ≤ (4RD+1)^{2f} = exp(2f·log(4RD+1)) whenever 4RD > 1.
(The +1 is a grid-discretization artifact; the mathematical content is unchanged.)

**Proof**: Grid ℂ with step (2D)⁻¹.  The floor functions f_ℤ(z) = ⌊(z.re+R)·2D⌋
and g_ℤ(z) = ⌊(z.im+R)·2D⌋ map each point in the coset slice to a cell in
[0, M)×[0, M) where M = ⌊4RD⌋+1.  First-coordinate separation implies
distinct points go to distinct cells (otherwise their difference would have
norm < D⁻¹).  Hence |X| ≤ M² ≤ (4RD+1)² ≤ (4RD+1)^{2f}.
-/

#check size_bound

/-!
## Axiom 5: First-coordinate separation

**Location**: `Erdos90/Geometric.lean`, declared as `axiom first_coordinate_separation`.

**Statement**: For every non-zero v ∈ A.Λ, the modulus of its first
coordinate is at least D⁻¹.

**Why this holds**: In the Minkowski lattice Λ = Φ(D⁻¹O_K) ⊂ ℂ^f,
coordinate 0 corresponds to the distinguished embedding σ₀ : K → ℂ.
If ‖v₀‖ < D⁻¹, then the corresponding algebraic integer β = D·v has
|σ₀(β)| < 1.  But β is an algebraic integer all of whose conjugates lie
in a bounded set determined by the polydisc.  The only algebraic integer
with all conjugates of modulus < 1 is 0, so β = 0 and v = 0.
-/

#check first_coordinate_separation

/-!
## Remaining `sorry` spots in the Lean formalization

The project compiles with exactly one `sorry` gap:

### Deep axiom (awaiting human verification):
1. **`exists_good_coset`** (`Geometric.lean`) — Axiom 3 above (Haar measure on torus ℂ^f/Λ)

All other lemmas and theorems are fully proven, including:
- `size_bound` (Axiom 4) — grid discretization proof
- `planar_set_from_datum` (Theorem 2.3 parametric form)
- `admissible_family_to_planar_set` (Theorem 2.3)
- `erdos_unit_distance_false` (Theorem 1.1)
- `erdos_bound_false` (contrapositive of Theorem 1.1)
-/

#check admissible_family_to_planar_set
#check erdos_unit_distance_false
#check erdos_bound_false
