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

There are **2 remaining axioms**, both in `Erdos90/NumberField.lean`:
`prop_3_2_to_3_6` and `prop_2_2`.

`prop_2_2` is now only the U-construction (class-group pigeonhole producing
norm-1 elements). The coset averaging part (Lemma 2.4 of the paper) is split
into a separate `def lemma_2_4`, which is structurally proved but has `sorry`
gaps for the measure-theoretic unfolding identities.

`exists_admissible_family` is a **theorem** (proved in `NumberField.lean`
from these 2 axioms + `lemma_2_4` + the analytic lemmas `prop_p6` and
`hlog2_event`, both fully proved).

`C_class := 1` is a concrete `def`, not an axiom.
`C₀` and `prop_3_7` are absorbed into the axioms above.
-/

open Real

noncomputable section

/-!
## Axiom 1: Golod–Shafarevich / Chebotarev tower construction
   (Propositions 3.2–3.6 of the paper)

**Location**: `Erdos90/NumberField.lean` line 68: `axiom prop_3_2_to_3_6`.

**Statement**: ∃ C_rd > 0 such that ∀ ℓ ≥ 2, ∃ D₀ > 0, rd_F ≥ 1 with
`log rd_F ≤ C_rd · ℓ · log ℓ`, and ∀ M, ∃ f ≥ M, lattice Λ ⊂ ℂ^f
with D₀-separation: nonzero Λ-elements have first coordinate ≥ D₀⁻¹.

**Mathematical input**:
- Prop 3.2: Cyclotomic base field F (cyclic cubic, totally real),
  conductor–discriminant formula, M/F unramified
- Prop 3.4: Golod–Shafarevich inequality (r > d²/4 ⇒ infinite pro-p group) [GS64]
- Prop 3.5: Shafarevich relation-rank estimate (r(G) ≤ d(G) + C₀) [Sha63]
- Prop 3.6: Chebotarev density theorem (t = ⌊(ℓ-1)²/100⌋ primes with
  Frobenius in Φ(G)) [Tsc26]
- Step 3: Tower layers with fⱼ → ∞, rd(Fⱼ) = rd(F)

**Absent from Mathlib**: Golod-Shafarevich, Chebotarev density,
class field towers, pro-p group cohomology.

**Verification**: Can only be verified on paper.  Combines group
cohomology [GS64, Sha63] with algebraic number theory [Neu99, Koc02].
-/

/-!
## Axiom 2: Class-group pigeonhole for norm-1 elements
   (Proposition 2.2 of the paper)

**Location**: `Erdos90/NumberField.lean` line 108: `axiom prop_2_2`.

**Statement**: Given f ≥ 1, D₀ > 0, t ≥ 0, log_H, and a lattice Λ
with D₀-separation, there exists U ⊂ ℂ^f such that:
- All coordinates of u ∈ U have modulus 1
- D₀·u ∈ Λ for all u ∈ U
- |U| ≥ exp((t·log 2 − log_H)·f)

**Mathematical input**:
- Prop 2.2: 2^{tf} binary vectors → h(K) ≤ H^f ideal classes →
  pigeonhole gives ≥ exp((t·log 2 − log H)·f) vectors sharing a class
- For each pair: u_ε = α_ε / c(α_ε) has |σ(u_ε)| = 1 for all
  complex embeddings σ

**Mathlib status**: Ideal class group, Minkowski bound, class number
computations — not available in Mathlib.

**Verification**: Combinatorial pigeonhole on the ideal class group.
(Prop 2.2 in the paper).

---

## Lemma 2.4: Coset averaging (def, partially proved)

**Location**: `Erdos90/NumberField.lean` line 168: `def lemma_2_4`.

Given f, Λ with fundamental domain F, U with |U| ≥ exp(γf), and
R > 1/2 with log ρ(R) > -γ/2, constructs a `CosetAvgWitness`.
The algebraic inequality |U|·ρ(R)^f ≥ exp(γf/2) is fully proved.
The measure-theoretic proof (unfolding trick, averaging principle)
has `sorry` gaps pending Mathlib's Haar measure / fundamental domain
API for ℂ^f/Λ.

**Mathematical input**:
- Lemma 2.4: Haar probability measure on ℂ^f/Λ, Fubini on a
  fundamental domain gives E_a[E] ≥ exp(γf/2)·E_a[N] → some coset
  a+Λ achieves E_a ≥ exp(γf/2)·N_a

**Verification**: Standard Fubini/averaging on a compact abelian group.
-/

#check exists_admissible_family
#check prop_3_2_to_3_6
#check prop_2_2
#check lemma_2_4
