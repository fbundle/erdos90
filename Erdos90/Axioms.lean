import Erdos90.Arithmetic
import Erdos90.NumberField
import Erdos90.Geometric
import Erdos90.Main

/-!
# Axioms (for human verification)

This file documents every postulate that the proof assumes without a
formal Lean derivation.  Each corresponds to a deep theorem in the
literature.

**All axioms should be reviewed by a number theorist / geometer.**

There are **3 remaining axioms**, all in `Erdos90/NumberField.lean`:
`prop_3_2_to_3_6`, `prop_2_2`, and `prop_2_2_covg`.

`exists_admissible_family` is a **theorem** (proved in `NumberField.lean`
from these 3 axioms + the analytic lemmas `prop_p6` and `hlog2_event`,
both fully proved).
-/

open Real

noncomputable section

/-!
## Axiom 1: Golod–Shafarevich / Chebotarev tower construction
   (Propositions 3.2–3.6 of the paper)

**Location**: `Erdos90/NumberField.lean`, line 68: `axiom prop_3_2_to_3_6`.

**Statement**: ∃ C_rd > 0 such that ∀ ℓ ≥ 2, ∃ D₀ > 0, rd_F ≥ 1 with
`log rd_F ≤ C_rd · ℓ · log ℓ`, and ∀ M, ∃ f ≥ M, lattice Λ ⊂ ℂ^f
with D₀-separation: nonzero Λ-elements have first coordinate ≥ D₀⁻¹.

**Mathematical input**:
- Prop 3.2: Cyclotomic base field F (cyclic cubic, totally real)
- Prop 3.4: Golod–Shafarevich inequality (r > d²/4 ⇒ infinite pro-p group)
- Prop 3.5: Shafarevich relation-rank estimate (r(G) ≤ d(G) + C₀)
- Prop 3.6: Chebotarev density theorem (split primes with trivial Frobenius)
- Step 3: Tower layers with fⱼ → ∞, rd(Fⱼ) = rd(F)

**Absent from Mathlib**: Golod-Shafarevich [GS64], Chebotarev [Tsc26],
class field towers, pro-p group theory.

**Verification**: Can only be verified on paper.  Combinatorial group
cohomology + algebraic number theory, totaling ~50 pages in [Neu99,
Koc02, Sha63].
-/

/-!
## Axiom 2: Class-group pigeonhole (Proposition 2.2)

**Location**: `Erdos90/NumberField.lean`, line 106: `axiom prop_2_2`.

**Statement**: Given f ≥ 1, D₀ > 0, t ≥ 0, log_H, and a lattice Λ
with D₀-separation, there exists U ⊂ ℂ^f such that:
- All coordinates of u ∈ U have modulus 1
- D₀·u ∈ Λ for all u ∈ U
- |U| ≥ exp((t·log 2 − log_H)·f)

**Mathematical input**:
- Prop 2.2: 2^{tf} binary vectors → h(K) ≤ H^f ideal classes → by
  pigeonhole, ≥ exp((t·log 2 − log H)·f) vectors share a class
- For each such pair (ε,η): u_ε = α_ε / c(α_ε) has |σ(u_ε)| = 1
  for all complex embeddings σ

**Absent from Mathlib**: Number field ideal-class structure, CM-field
complex conjugation, ideal norm bounds in terms of root discriminant.

**Verification**: Combinatorial pigeonhole on a finite group.  Valid
given Prop 3.7 (Minkowski) and the tower structure.
-/

/-!
## Axiom 3: Haar measure coset averaging (Lemma 2.4)

**Location**: `Erdos90/NumberField.lean`, line 117: `axiom prop_2_2_covg`.

**Statement**: Given all the data of Axioms 1 and 2 plus U with the
properties above, for any R > 1/2 with `log ρ(R) > −(t·log 2 − log_H)/2`,
there exists a `CosetAvgWitness` a, X such that the finite intersection
X = (a+Λ) ∩ B_R is nonempty and E ≥ exp(γf/2)·|X|, where E counts
ordered pairs (x,y) ∈ X² with y−x ∈ U.

**Mathematical input**:
- Haar probability measure on the compact torus ℂ^f/Λ
- 𝔼[|(a+Λ) ∩ B_R|] = vol(B_R)/covol(Λ) (Fubini on fundamental domain)
- 𝔼[E] = |U|·a(R)^f / covol(Λ) (overlap area for U-pairs)
- From log ρ(R) > −γ/2: a(R)^f > (πR²)^f·exp(−γf/2)
- With |U| ≥ exp(γf): ∫ E ≥ exp(γf/2)·∫ N → some coset achieves average

**Mathlib status**: `IsAddFundamentalDomain` + `MeasureTheory` machinery
exists but the specific integration identities for polydiscs and lattices
in ℂ^f are not developed.

**Verification**: Standard Fubini/averaging on a compact abelian group.
Would require ~200 lines of Lean measure-theoretic API.
-/

#check exists_admissible_family
#check prop_3_2_to_3_6
#check prop_2_2
#check prop_2_2_covg
