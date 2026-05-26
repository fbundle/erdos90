# D3.1 — Mathlib gap for class field theory + GS + Chebotarev

Survey of `vendor/mathlib4/Mathlib/` (v4.30.0-rc2 / master-2026-05-24) for the
infrastructure required to close `hmr_brd_cm_tower`.

## What Mathlib has (relevant building blocks)

### Galois theory
- `Mathlib/FieldTheory/Galois/Basic.lean` — `IsGalois`, `IsGalois.normal`,
  `IsGalois.separable`, fundamental theorem.
- `Mathlib/FieldTheory/Galois/Profinite.lean` — `Gal(K̄/K)` as a profinite group via
  `inverseLimit` of finite Galois groups.
- `Mathlib/NumberTheory/Cyclotomic/Gal.lean` — `Gal(ℚ(ζₙ)/ℚ) ≅ (ℤ/n)ˣ`.

### Frobenius & decomposition groups
- `Mathlib/NumberTheory/NumberField/Embeddings.lean` — `arithFrobAt` for unramified
  primes in a Galois extension. **Note: only for finite extensions, not for the limit.**
- `Mathlib/NumberTheory/RamificationInertia/` — `ramificationIdx`, `inertiaDeg`,
  `Decomposition` group basics.

### Profinite / cohomology
- `Mathlib/GroupTheory/Profinite/Basic.lean` — profinite groups as `CompactSpace` +
  `TotallyDisconnectedSpace` + `Group`.
- `Mathlib/RepresentationTheory/Homological/GroupCohomology/Basic.lean` — `H^n(G, M)`
  for *discrete* finite groups. **The continuous / profinite version is absent.**

### Class group / number field arithmetic
- `Mathlib/NumberTheory/NumberField/ClassNumber.lean` — finiteness, Minkowski bound,
  `exists_ideal_in_class_of_norm_le`.
- `Mathlib/NumberTheory/NumberField/CMField.lean` — `IsCMField`, complex conjugation.
- `Mathlib/NumberTheory/NumberField/Discriminant/Basic.lean` — `NumberField.rootDiscr`.

## What Mathlib is MISSING (the real blockers)

### 1. Class field theory (Artin reciprocity) — *completely absent*

There is **no** Artin reciprocity map in Mathlib. None of:
- The idele class group `C_K = 𝔸_K^× / K^×`
- The reciprocity isomorphism `Gal(K^ab/K) ≅ C_K`
- Local reciprocity `Gal(K_v^ab/K_v) ≅ K_v^×`
- Hilbert class field, ray class fields
- Conductor-discriminant formula

Existence of the Hilbert class field `H/K` with `Gal(H/K) ≅ Cl(K)` is the **first step**
of the GS class-field tower. Without it, `K → H(K) → H(H(K)) → …` cannot even be
formulated. **Estimated formalization effort: 12–24 months** (this is the elephant
in the room; Mathlib has been working toward it for years).

### 2. Pro-p group cohomology — *partial*

Mathlib has finite-group cohomology (`H^n(G, M)` for `[Finite G]`). For the GS
inequality we need *continuous* cohomology of profinite groups, with topological
modules. Concretely:

```
H^1_cont(G, 𝔽_p) = continuous Hom(G, 𝔽_p)  -- generator count
H^2_cont(G, 𝔽_p) = obstruction to lifting central extensions  -- relation count
```

Building this requires:
- Continuous group cohomology (Tate cohomology, profinite analog)
- The Frattini subgroup `Φ(G)` of a pro-p group; `G/Φ(G)` as `𝔽_p`-vector space
- `H^1_cont(G, 𝔽_p) = Hom(G/Φ(G), 𝔽_p)` (Burnside basis theorem, profinite version)

None of this is in Mathlib. **Estimated effort: 6–12 months** (depends on whether
Mathlib's existing finite cohomology can be reused via limits).

### 3. Golod–Shafarevich inequality — *absent*

The bare inequality `r < d²/4 ⇒ G infinite` for a finitely-presented pro-p group
with d generators and r relations. Statement is elementary once cohomology is in
place; proof is ~200–300 lines of careful counting.

### 4. Chebotarev density — *absent*

`Mathlib/NumberTheory/NumberField/Embeddings.lean` defines `arithFrobAt` but no
density statement. The bare existence of "infinitely many split primes" (which is
what Sawin's construction needs) follows from Chebotarev, but Chebotarev itself
needs:
- Dirichlet density (or natural density) for sets of primes
- Analytic continuation of L(s, χ) past s=1 for Galois characters χ
- The Frobenius-class equidistribution argument

The L-function side overlaps heavily with what `class_num_bound_of_brd` needs;
see `D32_analytic_class_number_mathlib_gap.md`.

**Estimated effort for Chebotarev alone: 6–12 months.**

### 5. Maximal extension unramified outside S — *absent*

`K_S(F)/F` is the compositum of all finite Galois extensions of `F` unramified
outside `S`. Mathlib has neither the construction nor the ramification filtration
needed to discuss "unramified outside S" for a non-finite extension.

## Critical path to closing D3.1

The dependency DAG:

```
ramification filtration  ←→  local class field theory
        ↓                            ↓
class field theory (global) ←——————┘
        ↓
Hilbert class field, class field tower
        ↓
Golod–Shafarevich inequality (uses pro-p cohomology)
        ↓
HMR's specific construction (small-rd CM base + GS criterion)
        ↓
hmr_brd_cm_tower (modulo Chebotarev for the split-prime piece)
```

Chebotarev runs in parallel through analytic L-functions (shared with D3.2).

## Recommended near-term action

Closing D3.1 is *not* achievable on a months timescale, but we can:

1. **Refactor the sorry** into 3–4 named sub-postulates per `D31_hmr_brd_what_we_need.md`,
   so the dependency on each Mathlib subsystem is named.
2. **Track Mathlib PRs**:
   - Watch `leanprover-community/mathlib4` for `ClassField`, `ProFiniteCohomology`,
     `Chebotarev`, `ArtinReciprocity` keywords.
   - https://github.com/leanprover-community/mathlib4/labels/t-number-theory
3. **Contribute the easy pieces**: `Nat.dvd_factorial` chains, Minkowski bound
   refinements (`minkBound_le_pow_rootDiscr` style), `IsCMField` lemmas — these
   land in Mathlib PRs and reduce the surface area when the big pieces arrive.

The honest answer is **D3.1 will close when Mathlib closes Artin reciprocity**,
likely in 2027–2028.
