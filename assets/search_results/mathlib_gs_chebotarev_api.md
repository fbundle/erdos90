# Mathlib v4.29.1 — Golod–Shafarevich Tower and Chebotarev Density API Audit

Sources searched:
- vendor/mathlib4/Mathlib/GroupTheory/Profinite/
- vendor/mathlib4/Mathlib/NumberTheory/NumberField/
- vendor/mathlib4/Mathlib/NumberTheory/Cyclotomic/
- arXiv:2605.20579 (Sawin 2026), arXiv:0809.2742 (Ershov survey),
  arXiv:1008.3002 (Hajir-Maire-Ramakrishna), arXiv:2406.00797

---

## A. Golod–Shafarevich in Mathlib — STATUS: MISSING

### What exists

```lean
-- Profinite groups (GroupTheory/Profinite/Basic.lean)
structure ProfiniteGrp : Type (u+1)  -- category of profinite groups

-- Profinite completion
ProfiniteGrp.ofFreeGroup : FreeGroup α → ProfiniteGrp
```

**MISSING**: No GS inequality, no Frattini quotient rank bound, no infinite tower criterion.

### The GS inequality (needed)

For a pro-p group G with d(G) = dim_𝔽_p(G/Φ(G)) (generator rank) and
r(G) = dim_𝔽_p(H²(G, 𝔽_p)) (relation rank):

```
r(G) ≤ d(G)²/4  →  G is infinite  (Golod–Shafarevich 1964)
```

The pro-p group structure for Sawin's construction: let S = {3,5,7,...,43}
(the 13 smallest odd primes except p=2). For the p=3 Sawin instance:
- T = {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43}  (13 primes, all ≡ 1 mod 3 needed)
- d(G) ≥ 12 (from T-rank of class field tower)
- r(G) ≤ d(G)²/4 = 144/4 = 36

This gives an infinite pro-3 tower F = F₀ ⊂ F₁ ⊂ F₂ ⊂ ... with
rd(Fₙ) bounded (root discriminant stays bounded by Odlyzko bounds).

### Formalization effort

Estimated: **2000–5000 lines** to formalize GS inequality and pro-p class field towers in Lean 4.
Required imports: group cohomology (partially in Mathlib), inflation-restriction sequence,
Frattini subgroup, p-adic Lie groups. None of the pro-p tower machinery exists.

### Key references

- Golod–Shafarevich (1964), Izv. Akad. Nauk SSSR, Mat. 28
- Ershov survey: arXiv:0809.2742 — "Golod-Shafarevich groups: a survey"
- Hajir–Maire (2001), Compositio Math 130: bounds on rd for towers
- Hajir–Maire–Ramakrishna: arXiv:1008.3002 — "Infinite class field towers of number fields"
- arXiv:2406.00797 — recent results on bounded-discriminant towers

---

## B. Chebotarev Density Theorem in Mathlib — STATUS: MISSING

### Frobenius elements (AVAILABLE, limited)

```lean
-- NumberField/Embeddings.lean (added ICMS 2024)
NumberField.arithFrobAt (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] (p : ℕ) [Fact (Nat.Prime p)] (hp : p.Coprime (discr K)) :
    Gal(K/ℚ)
-- Returns the Frobenius element at p; existence proved
```

**MISSING**: No density statement, no equidistribution, no "infinitely many primes with given Frobenius."

### Chebotarev density theorem (needed)

The version needed for Sawin's split-prime existence:

> For a Galois extension K/ℚ with group G, and any conjugacy class C ⊆ G,
> the set of primes p with Frob_p ∈ C has Dirichlet density |C|/|G|.

In particular: primes that split completely in K/ℚ (Frob_p = id) have density 1/[K:ℚ] > 0,
hence there are infinitely many such primes.

### What split-prime existence requires

For Sawin's `exists_cm_class_group_data`, we need:

```lean
-- Needed (not in Mathlib):
theorem exists_split_primes (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] (m : ℕ) :
    ∃ (S : Finset (Ideal (𝓞 K))), S.card = m ∧
      ∀ 𝔓 ∈ S, 𝔓.IsMaximal ∧
        Ideal.ramificationIdx (algebraMap ℤ (𝓞 K)) (𝔓.under ℤ) 𝔓 = 1 ∧
        Ideal.inertiaDeg (algebraMap ℤ (𝓞 K)) (𝔓.under ℤ) 𝔓 = 1
```

Chebotarev guarantees density 1/[K:ℚ] of such primes, so infinitely many exist.

### Formalization effort

Estimated: **5000–10000 lines** to formalize Chebotarev density in Lean 4.
Required: L-functions, Dirichlet series, analytic continuation, residue at s=1.
The Lean Chebotarev project (lean-chebotarev, 2023) covers a weaker form only
(Frobenius equidistribution mod finite sets, not Dirichlet density).

---

## C. Bounded Root Discriminant Towers — STATUS: MISSING

### Odlyzko bounds (needed for GSTowerData.hlog_rd)

The Minkowski-Odlyzko lower bound: for a totally complex number field K of degree n,
```
rd(K) ≥ 4π e^{γ+1} ≈ 22.3  (asymptotic lower bound as n → ∞)
```
The Golod–Shafarevich tower stays below the Martinet-Pohst bound ≈ 92.4.

**MISSING**: No Odlyzko bounds in Mathlib. No `discriminant_lowerBound` theorem.

### What the project uses instead

`GSBaseData` takes `hlog_rd : Real.log (rd_F) ≤ C_ell * Real.log ℓ` as a hypothesis
(Prop 3.2 in the formalization). This is asserted via `sorry` in `gs_tower_levels` and is the
`hΛ_sep` sub-sorry that cannot be filled without the GS tower.

---

## D. Summary Table

| Feature | Mathlib Status |
|---|---|
| `ProfiniteGrp` (structure) | **AVAILABLE** |
| Frattini subgroup of pro-p group | **MISSING** |
| GS inequality r(G) ≤ d(G)²/4 → G infinite | **MISSING** |
| Pro-p class field tower construction | **MISSING** |
| Bounded root discriminant tower | **MISSING** |
| `arithFrobAt` (Frobenius element existence) | **AVAILABLE** |
| Chebotarev density theorem | **MISSING** |
| "Infinitely many split primes" | **MISSING** |
| Odlyzko discriminant lower bounds | **MISSING** |
| Relative class number h⁻(K) = h(K)/h(K⁺) | **MISSING** |
| GS tower CM field K with `Module.finrank ℚ K = 2f` | **MISSING** |

---

## E. Concrete Sawin Parameters (arXiv:2605.20579, §3)

The paper uses a pro-3 tower over ℚ ramified at T:

```
p = 3
T = {primes q : q ≡ 1 (mod 3), q ≤ 43}
  = {7, 13, 19, 31, 37, 43}  (or larger set for stronger bounds)
```

The rank bounds:
- d(Gal(F^{T,3}/F)) ≥ |T| - 1 (by class field theory + Grunwald-Wang)
- r(Gal(F^{T,3}/F)) ≤ |T|²/4 (by GS + Burnside basis theorem)
- GS criterion: if |T| > 4, the tower is infinite

For the formalization to give K with `Module.finrank ℚ K = 2f`, the tower
provides fields Fₙ with [Fₙ : ℚ] = 2f for appropriate n and T.

---

## F. Recommended Literature for Future Formalization

1. **Sawin 2026** (arXiv:2605.20579) — defines the exact construction used here
2. **Ershov 2008** (arXiv:0809.2742) — best survey of GS inequality and pro-p groups
3. **Hajir–Maire 2001** (Compositio 130, 65–75) — root discriminant in towers
4. **Hajir–Maire–Ramakrishna** (arXiv:1008.3002) — infinite towers with bounded discriminant
5. **Koch 2002** — "Galois Theory of p-Extensions" (Springer monograph) — pro-p foundations
6. **Neukirch–Schmidt–Wingberg** (Cohomology of Number Fields, 2008) — cohomological GS
