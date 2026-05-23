# CM Field Construction References for Lean Formalization

Generated: 2026-05-24. Source: web search across arXiv, Mathlib docs, textbooks.

---

## 1. CM Fields and the Mixed Embedding

### Definition and Key Property

A CM field is a totally imaginary quadratic extension K/F where F is totally real. For K totally
complex (r1=0, r2=f, [K:Q]=2f), the **mixed embedding** is:

    Phi: K -> product_{v in Sigma_{F,inf}} K_v = C^f

where Sigma_{F,inf} is the set of infinite places of F, each K_v = C. In Mathlib this corresponds
to `NumberField.mixedEmbedding` mapping into `mixedSpace K = ({w : IsReal w} -> R) x ({w :
IsComplex w} -> C)`, but for totally complex K the real part is empty, so the space is isomorphic
to C^f.

**Critical CM property** (Remarks paper §2.1, Remark after Lemma 2.2):

> "An element of a CM field has absolute value 1 in some embedding if and only if it has absolute
> value 1 in all embeddings."

**Proof sketch**: If phi: K -> C is a complex embedding and c is complex conjugation on K, then
the other embeddings are {sigma ∘ phi : sigma in Gal(K/Q)}. For a CM field, c commutes with all
automorphisms. If |phi(alpha)| = 1 then |phi(alpha)|^2 = phi(alpha) * conj(phi(alpha)) =
phi(alpha) * phi(c(alpha)) = phi(alpha * c(alpha)). So alpha * c(alpha) is totally real and
positive with phi-value 1. Since alpha * c(alpha) lies in F and equals 1 in one real embedding
and is totally positive, it equals 1 in all real embeddings. Hence |sigma(alpha)|^2 = sigma(alpha
* c(alpha)) = 1 for all sigma.

---

## 2. The Map alpha -> alpha/c(alpha) and Norm-One Elements

### The Pigeonhole Construction (Sawin Lemma 7, arXiv:2605.20579 p.6-7)

Let K/F be a CM extension (K totally imaginary, F totally real, [F:Q]=d). Let c = generator of
Gal(K/F) acting as complex conjugation. Let N_{K/F} be the relative norm map on fractional
ideals. Let SF be a set of prime ideals of O_F, each splitting in K/F, and k: SF -> Z_{>0}.
Define:

    L = {J ideal of O_K : N_{K/F}(J) = product_{p in SF} p^{k(p)}}

Then:
- #L = product_{p in SF} (k(p) + 1)  [each split prime p = p1*p2 in K contributes k(p)+1 choices
  of ideal p1^j * p2^{k(p)-j}]
- The map L -> GK (a group of size <= 2^{d+1} * h^-(K)) has a fiber of size >= #L / #GK

**The fiber gives norm-1 elements via**: from two ideals J, J' in the same GK-fiber, the ratio
J*J'^{-1} is principal, say J*J'^{-1} = (beta). Then N_{K/F}(beta) = 1. Writing u = beta/c(beta):
- u is an element of K with |u|_v = 1 for all archimedean v (by the CM property)
- u lies in p^{-2k} * O_K where p is the scaling factor

**Simplified version (Remarks paper Lemma 2.2)**: Apply pigeonhole to ideals
{product_j P_j^{a_j} * Pbar_j^{k_j - a_j} : 0 <= a_j <= k_j}. Two ideals in the same ideal
class give alpha with (alpha) = I1 * I2^{-1}, then u = alpha/alphabar satisfies |u| = 1
everywhere, and #U >= product(k_j+1) / h(K).

**Proof that |beta/c(beta)| = 1**: For any complex embedding phi:
    |phi(beta/c(beta))| = |phi(beta)| / |phi(c(beta))| = |phi(beta)| / |conj(phi(beta))| = 1.

This is `cm_norm_div_conj_eq_one` in the existing Lean code — already proved.

### Injectivity / Distinctness (for `hmk_unit_inj`)

From Remarks paper proof of Lemma 2.2 (p.6):

> "The ideals (u) = (alpha^2) are pairwise distinct."

For two alpha, alpha' from different ideal classes, the ideals (alpha/alphabar) =
(alpha)^2 * (alphabar)^{-2} differ because (alpha) and (alpha') are in different ideal classes.
Key injectivity: **u = alpha/alphabar determines the ideal class of (alpha)^2 in Cl(K)**.
Distinct ideal class pairs yield distinct u.

**What the Lean proof needs**: Injectivity of mk_unit on a fiber amounts to showing distinct
representatives in L give distinct beta/c(beta). Since (beta/c(beta)) = (beta)^2 * (c(beta))^{-2}
as ideals, and distinct J in the same GK-fiber give distinct J^2 (because the kernel of squaring
in Cl(K) is finite and controlled), the images are distinct. This avoids direct valuation parity
and replaces it with ideal-theoretic injectivity in Cl(K).

### The Sawin GK Group (Lemma 6)

The group GK is defined as pairs (J, u) where J is a fractional ideal and u generates N_{K/F}(J),
up to (J,u) ~ ((alpha)J, alpha*c(alpha)*u) for alpha in K^*. This fits into the exact sequence:

    O_K^* -> O_F^* -> GK -> Cl(K) -> Cl(F)

where all maps are the relative norm. Key bound: #GK <= 2^{d+1} * h^-(K) where
h^-(K) = h(K)/h(F) is the relative class number.

---

## 3. Split Primes and Valuation Parity

### Why Split Primes Give Independent Elements

For K a CM field with complex conjugation c, a rational prime p that **splits completely** in K
means p*O_K = product_{i} P_i * c(P_i) where P_i != c(P_i).

**Valuation parity constraint**: For u in O_K with |u|_v = 1 for all archimedean v (a "norm-one"
element), the product formula gives product_v |u|_v = 1 over all places v. Since |u|_v = 1 for
all archimedean v, product_{non-arch v} |u|_v = 1. For a split prime P with conjugate cP:

    v_P(u) + v_{cP}(u) = 0

This is because N_{K/F}(u) = u*c(u). For u = alpha/c(alpha): N_{K/F}(u) = (alpha/c(alpha)) *
c(alpha/c(alpha)) = (alpha/c(alpha)) * (c(alpha)/alpha) = 1. So N_{K/F}(u) = 1, which means for
each prime p of F split as p = P*cP: v_P(u) + v_{cP}(u) = 0.

**Reference** (arXiv:2507.10387, Akhtari-Vaaler-Widmer):
> "For a prime p splitting in K as p = P*P', valuations satisfy v_P(alpha) = -v_{P'}(alpha) for
> norm-one elements alpha."

**For `hmk_unit_inj`**: Injectivity follows from: if mk_unit(alpha) = mk_unit(alpha'), then
alpha/c(alpha) = alpha'/c(alpha'), so alpha*c(alpha') = alpha'*c(alpha). Setting gamma =
alpha/alpha', we get gamma = c(gamma), so gamma lies in F (the totally real subfield). Within the
pigeonhole fiber, alpha and alpha' generate the same ideal modulo F^*, so alpha and alpha' are
equal in the fiber quotient. The cleaner Lean path: use that (alpha/c(alpha)) determines
(alpha)^2 as a fractional ideal, and distinct fiber representatives by construction give distinct
squares.

---

## 4. Golod-Shafarevich Tower Construction

### The Theorem

**Golod-Shafarevich Theorem** (1964, Vinberg-Gaschütz refinement 1967):
For a pro-p group G with d(G) = minimal generators and r(G) = minimal relations:
G is infinite if r(G) <= d(G)^2 / 4.

**Application**: For K an imaginary quadratic field with t odd ramified primes, the 2-rank
satisfies d2(Cl(K)) >= t - 1. The Galois group G of the maximal unramified 2-extension satisfies
r(G) - d(G) <= 1 (Shafarevich 1963). Therefore if d(G) >= 5 (i.e., t >= 6), the inequality
r(G) <= d^2/4 holds: with d=5 we get r <= 6 <= 25/4 = 6.25.

**Worked example** (Zhou thesis, Harvard): T = {3,5,7,11,13,17}, S = {101, inf}. Then
L_T = Q(sqrt(5), sqrt(13), sqrt(17), sqrt(21), sqrt(33)), 101 splits in L_T, d(G_T^S) = 5,
r(G_T^S) <= 6, and 6 <= 25/4. So G_T^S is infinite.

**The explicit construction from Remarks paper (Proof of Theorem 1.1, p.5)**:
Let T be any finite set of odd primes with |T| >= 6. Let G_T = Galois group of maximal pro-2
extension of Q unramified outside T. Then:
- d(G_T) = |T| - 1 (if T contains a prime = 3 mod 4) or |T| (otherwise)
- For S = {p, inf} with p a prime splitting completely in L_T(i):
  d(G_T^S) = d(G_T), r(G_T^S) <= d(G_T) + |S| - 1
- Condition for infinitude: |T| - 1 + |S| - 1 <= (|T| - 1)^2 / 4

**Sawin's Lemma 11 and 12** give precise parameters: starting from the quadratic field
Q = Q(sqrt(product_{q in T} q)), build totally real Galois extensions F of Q that are everywhere
unramified with controlled inertia degrees for primes in SQ, then take K = F(sqrt(-1)) as the
CM field.

**Resulting root discriminant**: rd_{K/F} = 4 * product_{q in T} q

**Discriminant bound**: For L in the tower (totally real, ramified only at T), since ramification
at T is tame: |Disc L| <= product_{p in T} p^[L:Q], so rd(L) <= product_{p in T} p.
For K = L(i): rd(K) <= product_{p in T union {2}} p =: r.

**For `gs_tower_levels` in Lean**: The core gap is constructing the tower fields {L_j} with
[L_j : Q] -> inf, bounded root discriminant, and a fixed rational prime p splitting completely
in each L_j(i). Lean needs a constructive version producing actual fields F_j rather than just
asserting their existence. Golod-Shafarevich is not formalized in Mathlib v4.29.1.

---

## 5. Minkowski Lattice: Separation and Covolume

### The Separation Property (for `hLambda_sep` and `cmSeparation`)

For Lambda = Phi(D_0^{-1} * O_K) in C^f, the separation property says: for nonzero v in Lambda,
at least one coordinate v_i satisfies |v_i| >= D_0^{-1}.

**Proof**: Any nonzero alpha in O_K has algebraic norm N_{K/Q}(alpha) = product_{phi} |phi(alpha)|^2
which is a nonzero integer, hence >= 1. If all |phi_i(alpha)| < 1, then N_{K/Q}(alpha) < 1,
contradiction. So max_i |phi_i(alpha)| >= 1. Scaling: max_i |v_i| = D_0^{-1} * max_i |phi_i(alpha)|
>= D_0^{-1}.

**In Lean**: This should follow from:
- `canonicalEmbedding.norm_le_iff` giving: `‖canonicalEmbedding K x‖ ≤ r ↔ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ r`
- `Algebra.norm_ne_zero` for nonzero integral elements
- `Int.one_le_abs` (nonzero integers have |·| >= 1)
- `NumberField.Algebra.norm_eq_prod_embeddings` relating algebraic norm to product of embedding values

**The key Mathlib path**: `norm_ne_zero` + product formula + sup >= geometric mean argument.

**Sawin Lemma 4 (general version)**:
For any nonzero beta in I (a fractional ideal of O_K):
    sup_v |beta|_v / sqrt(|alpha|_v) >= (#(N_{K/F}(I) / (alpha)))^{-1/(2d)}

where alpha generates N_{K/F}(I). Proof: by product formula calculation (Sawin Lemma 3):
    product_{v in Sigma_{F,inf}} |beta|_v^2 / |alpha|_v = #(I/(beta)) / #(N_{K/F}(I)/(alpha)) >= 1 / #(N_{K/F}(I)/(alpha))

Taking d-th root and sup >= (product)^{1/d} gives the bound.

### Covolume Formula

    covol(O_K in C^f) = 2^{-f} * sqrt(|Disc K|)

This follows from `volume_fundamentalDomain_latticeBasis` in Mathlib, which gives:
    volume(fundamentalDomain(latticeBasis K)) = (2)^{-nrComplexPlaces K} * sqrt(‖discr K‖₊)

**The v-parameter inequality** (Remarks paper proof of Theorem 1.1, p.5):
    covol(p^{-2k} * O_{K_j}) = 2^{-f_j} * p^{-4k*f_j} * sqrt(|Disc K_j|)

Setting delta = p^{-2k}: v = r/2 satisfies v >= delta^{-2} * covol(...)^{1/f_j}
where r = product_{q in T union {2}} q is the root discriminant bound.

### First-Coordinate Injection

The projection onto any one complex coordinate C is injective on Lambda because K -> C by a complex
embedding is injective on K itself. Distinct lattice points with the same first coordinate would
give a nonzero K-element mapping to 0 under an embedding — impossible since embeddings are
injective ring homomorphisms.

**In Mathlib**: `NumberField.mixedEmbedding` restricted to totally complex K composed with any
coordinate projection is a ring homomorphism K -> C, hence injective.

---

## 6. Verified Mathlib API

From `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/Basic.lean`:
- `NumberField.mixedEmbedding (K : Type) : K →+* mixedSpace K`
- `NumberField.canonicalEmbedding.norm_le_iff {K} (x : K) (r : R) : ‖canonicalEmbedding K x‖ ≤ r ↔ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ r`
- `NumberField.canonicalEmbedding.integerLattice.inter_ball_finite K r`
- `ZSpan.isAddFundamentalDomain`
- `ZSpan.volume_fundamentalDomain : volume (fundamentalDomain b) = ENNReal.ofReal |(Matrix.of ⇑b).det|`
- `ZSpan.fundamentalDomain_isBounded`
- `Basis.ofZLatticeBasis`

From `Mathlib/NumberTheory/NumberField/CMField.lean`:
- `IsCyclotomicExtension.isCMField` — cyclotomic extensions are CM for n > 2
- `IsCMField.complexConj` — the complex conjugation automorphism c : K ≃ₐ[F] K
- `IsCMField.complexEmbedding_complexConj` — phi ∘ c = conj ∘ phi

From `Mathlib/NumberTheory/NumberField/ClassNumber.lean`:
- `exists_ideal_in_class_of_norm_le` — every ideal class has a rep with norm <= Minkowski bound

From `Mathlib/NumberTheory/NumberField/Discriminant/`:
- `discr_prime_pow` — explicit discriminant formula for ℚ(ζ_{p^k})

**NOT in Mathlib v4.29.1**: Golod-Shafarevich, quantitative Chebotarev (with explicit bounds),
relative class number h^-(K), pro-p group theory, tower existence.

---

## 7. Proof Strategy for Remaining Sorries

### `hLambda_sep` / `cmSeparation` (first-coordinate separation)

**Cleanest Lean proof**:
1. Let alpha be a nonzero element of O_K.
2. `have h_norm_ne_zero : Algebra.norm ℤ alpha ≠ 0` from `Algebra.norm_ne_zero` + `alpha ≠ 0`
3. `have h_norm_ge_one : |Algebra.norm ℤ alpha| ≥ 1` from `Int.one_le_abs` + step 2
4. `have h_prod : ∏ phi, ‖phi alpha‖^2 = |Algebra.norm ℤ alpha|` from `norm_eq_prod_embeddings`
5. `have h_max : ∃ phi, ‖phi alpha‖ ≥ 1` by contradiction (if all < 1, product < 1 contradicts step 3)
6. The specific coordinate with max norm satisfies the bound.

**Remaining gap**: Reordering embeddings so this max-norm coordinate is at index `fin0`. This
requires either (a) defining the embedding ordering so the max is always at 0 (not canonical), or
(b) showing the separation property doesn't require a specific coordinate — it just requires *some*
coordinate to be large, and the AdmissibleFamily `hLambda_sep` field says `‖v (fin0 A.hf)‖ ≥ A.D⁻¹`.
So the reordering question is crucial: the proof needs the *first* coordinate to be the large one.

**Resolution**: For the Remarks paper construction, the specific CM field K_j is constructed with
a distinguished embedding phi_0 that is the "dominant" one (e.g., the one corresponding to the
split prime P in the tower construction). The AdmissibleFamily.D is set to be the max over all
coordinates, and fin0 is the argmax coordinate. This requires choosing the embedding ordering
carefully when constructing the AdmissibleFamily.

### `hmk_unit_norm` — already proved as `cm_norm_div_conj_eq_one`

The proof is complete in the Lean code. Threading it through `exists_cm_class_group_data` requires
instantiating the CM field K and applying the existing lemma.

### `hmk_unit_inj` — ideal class injectivity

**Cleanest Lean approach (avoiding split-prime valuation)**:
The map mk_unit: alpha ↦ alpha/c(alpha) satisfies: the ideal (alpha/c(alpha)) = (alpha)^2 *
(c(alpha))^{-2}. Two distinct ideal classes [J] ≠ [J'] in the fiber of the norm-1 map give
beta, beta' with (beta) = J, (beta') = J'. Then (beta/c(beta)) = J^2/c(J)^2 and
(beta'/c(beta')) = J'^2/c(J')^2. If these are equal as ideals, then J^2/J'^2 = c(J)^2/c(J')^2,
i.e., (J/J')^2 is principal with generator in F. In the fiber, J/J' already satisfies that
N_{K/F}(J/J') is principal in O_F; the extra constraint from (J/J')^2 being in F means
J/J' is a 2-torsion class in Cl(K)/Cl(F). The fiber size is bounded correctly accounting for this.

---

## 8. Key References

| Source | Relevant content |
|--------|-----------------|
| Sawin, arXiv:2605.20579 | Lemmas 4–12: explicit construction with parameters, split primes, GK group |
| Remarks, arXiv:2605.20695 | Lemma 2.1 (separation), 2.2 (norm-1 elements), Theorem 1.1 proof outline |
| Zhou, Harvard thesis | Golod-Shafarevich theorem proof, class field tower construction, explicit examples |
| Akhtari-Vaaler-Widmer, arXiv:2507.10387 | Equidistribution of norm-1 elements, valuation parity |
| Neukirch, ANT §II.5 | Minkowski embedding, fundamental domain, covolume formula |
| Neukirch, ANT §VII.1 | CM fields, complex multiplication, norm-1 torus |
| Milne, CM.pdf | CM field theory, the map alpha/c(alpha), Shimura-Taniyama formula |
| Ershov survey on GS groups | Golod-Shafarevich inequality, applications to class field towers |
| Hajir-Maire, Compositio 2002 | Tamely ramified towers and discriminant bounds |
| Mathlib CanonicalEmbedding/Basic.lean | `norm_le_iff`, `integerLattice`, `latticeBasis` |
| Mathlib CMField.lean | `IsCMField.complexConj`, `complexEmbedding_complexConj` |
| Mathlib ClassNumber.lean | `exists_ideal_in_class_of_norm_le` |
