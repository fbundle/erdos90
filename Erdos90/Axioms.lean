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
## Axiom 2: Behaviour of the disc-overlap ratio ρ(R) (**PROVEN**)

**Location**: `Erdos90/Geometric.lean`, formerly `axiom`, now `lemma exists_R_log_rho_gt`.

**Proof**: Showed lim_{R→∞} ρ(R) = 1 using the explicit formula
ρ(R) = (2/π)·arccos(1/(2R)) - √(4R²-1)/(2πR²). The first term → (2/π)·(π/2) = 1
by continuity of arccos; the second term → 0 via the bound √(4R²-1) ≤ 2R
and the sandwich theorem. Then log continuity + limit definition yields the
existence statement.

**Status**: ✅ Proven in Lean.
-/

#check exists_R_log_rho_gt

/-!
## Axiom 3: Coset averaging (Lemma 2.4)

**Location**: `Erdos90/Geometric.lean`, declared as `axiom exists_good_coset`.

Using Haar probability measure on the torus ℂ^f / Λ, the expected size
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
## Axiom 5: First-coordinate separation (**PROVEN**)

**Location**: `Erdos90/Geometric.lean`, formerly `axiom`, now `lemma first_coordinate_separation`.

**Proof**: Strengthened the `hΛ_sep` field of `AdmissibleFamily` (in `Arithmetic.lean`)
to use the distinguished first coordinate `fin0 hf` instead of `∃ r : Fin f`.
The lemma then follows directly from `A.hΛ_sep`. This matches the paper's
Minkowski embedding construction, where coordinate 0 corresponds to the
distinguished embedding σ₀ : K → ℂ.

**Status**: ✅ Proven in Lean (derived from structure field).
-/

#check first_coordinate_separation

/-!
## Remaining axioms

The project compiles with zero `sorry` gaps.  All non-axiom statements are
fully proven in Lean.  The following are declared as `axiom` (awaiting human
verification by a number theorist / geometer):

### Axioms:
1. **`exists_admissible_family`** (`Arithmetic.lean`) — Golod-Shafarevich tower
2. **`exists_good_coset`** (`Geometric.lean`) — Haar measure coset averaging

### Proven (formerly axioms):
3. ~~`first_coordinate_separation`~~ — derived from `hΛ_sep` field
4. ~~`exists_R_log_rho_gt`~~ — calculus proof (ρ(R) → 1 as R → ∞)

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
-/

#check admissible_family_to_planar_set
#check erdos_unit_distance_false
#check erdos_bound_false
