# Structure API documentation

The Erd46 formalization uses several key structures to bridge between the
geometric and number-theoretic layers.  This document describes each
structure's purpose, fields, and usage.

## `AdmissibleFamily` (in `Erdos90/Arithmetic.lean`)

Top-level structure consumed by the geometric construction
(`admissible_family_to_planar_set` in `Geometric.lean`).

**Fields:**
- `f : ℕ` — degree (corresponds to `nrComplexPlaces K` in the BRD tower)
- `hf : f ≥ 1` — positivity
- `D : ℝ`, `hD : D > 0` — separation constant (`Q²` from the BRD tower)
- `γ : ℝ`, `hγ : γ > 0` — exponential growth rate (= `t·log 2 - log_H`)
- `Λ : AddSubgroup (Fin f → ℂ)` — the Minkowski lattice
- `U : Finset (Fin f → ℂ)` — finite set of norm-one elements
- `hU_mod` — all coords of all u ∈ U have modulus 1
- `hU_in_Λ` — U ⊆ Λ
- `hU_size` — `|U| ≥ exp(γ·f)`
- `hΛ_sep` — separation: every nonzero v ∈ Λ has some coord with `‖v i‖ ≥ D⁻¹`
- `hΛ_inj` — projection to first coordinate is injective on Λ
- `h_coset_avg` — coset averaging witness (uses `CosetAvgWitness`)

**Constructed by:** `exists_admissible_family` (in `NumberField.lean`).

**Consumed by:** `admissible_family_to_planar_set` (in `Geometric.lean`).

## `BRDTowerData ℓ` (in `Erdos90/NumberFieldDeep_GSTower.lean`)

Output of the BRD CM tower construction.  Phase D5 / D3.1 abstracts the
HMR 2021 / Chebotarev existence into this structure.

**Fields:**
- `Q : ℕ`, `hQ_pos : 0 < Q` — fixed tower constant (product of split primes)
- `D₀ : ℝ`, `hD₀_pos : D₀ > 0`, `hD₀_eq : D₀ = Q²` — derived separation
- `rd_F : ℝ`, `hrd_F_ge1 : 1 ≤ rd_F`,
  `hlog_rd : log rd_F ≤ ℓ · log ℓ` — root discriminant bound
- `getTowerLevel : ∀ (M, t, log_H, …), ∃ K f sp …` — the level-extractor
  callback.  Returns a CM totally complex K of complex degree f ≥ M with
  `rootDiscr K ≤ rd_F` and `SplitPrimeData K (t'·f)` having `sp.Q = Q`,
  along with the class-number bound `log(h_K)/f ≤ log_H`.

**Constructed by:** `brd_tower_data ℓ hℓ` (depends on sorries `gs_cm_tower`
and `chebotarev_fixed_Q`).

**Consumed by:** `brd_cm_tower_postulate` (PROVED Lean code modulo
`brd_tower_data`).

## `CMTowerData f hf1 Λ K` (in `Erdos90/NumberFieldDeep_CM.lean`)

Tower-level data for a specific CM field K.  Packages the embedding,
split-prime data, lattice membership, and class-number bound.

**Fields:**
- `φ : K →* ℂ` — the chosen complex embedding (with multiplicities) ...
- Various norm/conjugation properties
- `t'_param : ℕ` — split-prime parameter
- `spData : SplitPrimeData K (t'_param * f)`
- `h_div_conj_mem_Λ` — for the fixed spData, `Φ(α/c(α)) ∈ Λ` for valid α
- `classNumBound : ℝ`, `hClassNum : classNumBound ≤ ...`

**Constructed by:** `brd_cm_tower_postulate`.

**Consumed by:** `cm_norm_one_elements`, `exists_cm_class_group_data`.

## `CMClassGroupData f t log_H Λ` (in `Erdos90/NumberFieldDeep_CM.lean`)

Class-group pigeonhole data for Proposition 2.2.

**Fields:**
- `E : Type`, `[Fintype E]` — domain (split-prime sign vectors)
- `G : Type`, `[Fintype G]` — codomain (the class group)
- `φ : E → G` — the encoding map
- `cardE`, `cardG` — cardinalities
- `hcardE`, `hcardG` — explicit values
- `h_card_ratio : exp(γ·f) + 1 ≤ |E| / |G|`
- `mk_unit : E × E → K^×` (or similar) — the unit constructor
- `mk_unit_mem_Λ`, `mk_unit_norm`, `mk_unit_inj` — properties

**Constructed by:** `exists_cm_class_group_data`.

**Consumed by:** `cm_norm_one_elements`.

## `SplitPrimeData K m` (in `Erdos90/CMField/Basic.lean`)

Collection of `m` split-prime ideals in 𝓞_K, with conjugates distinct.

**Fields:**
- `Q : ℕ`, `hQ_pos : 0 < Q` — product of underlying rational primes
- `𝔓 : Fin m → IsDedekindDomain.HeightOneSpectrum (𝓞 K)` — the prime ideals
- `pairwise_ne_conj` — each is `≠` its complex conjugate
- `pairwise_distinct` — all 2m primes pairwise distinct
- `h_Q_count_at_split`, `h_Q_count_at_conj` — count properties (Phase B)

**Constructed by:** `splitPrimeData_from_prime_list` (Phase D2, from a list
of rational primes via the cyclotomic case) or `chebotarev_fixed_Q` (sorry).

**Consumed by:** `Q_sq_div_conj_mem_integers_of_spData` (Phase A integrality),
`CMTowerData` construction.

## `CosetAvgWitness f Λ U R γ` (in `Erdos90/Defs.lean`)

Output of Lemma 2.4 (coset averaging).

**Fields:**
- `a : Fin f → ℂ` — the chosen coset representative
- `X : Finset (Fin f → ℂ)` — the points in `(a + Λ) ∩ polydisc f R`
- `hX_sub`, `hX_fin`, `hX_ne` — basic properties
- `h_count : E ≥ exp(γ·f/2) · |X|` where E counts ordered U-pairs in X

**Constructed by:** `lemma_2_4` (in `CosetAveraging.lean`).

**Consumed by:** `exists_good_coset` in `Geometric.lean`, then by
`planar_set_from_datum` / `admissible_family_to_planar_set`.

## Data flow diagram

```
                  Erdős theorem (Main.lean)
                          ↑
            admissible_family_to_planar_set
                          ↑
                AdmissibleFamily  ←──── h_coset_avg ─── CosetAvgWitness
                          ↑                                    ↑
            exists_admissible_family                       lemma_2_4
                          ↑                                  (proved)
              prop_3_2_to_3_6_via_deep
                          ↑
       ┌──────────────────┼──────────────────┐
       ↓                  ↓                  ↓
golod_shafarevich   cm_norm_one_elements   class_num_bound_of_brd
   _tower            (PROVED)               (PROVED)
   _with_lattice                                ↑
       ↑                  ↑                ┌────┴────┐
   BRDTowerData      CMClassGroupData      E5      D3.2b
       ↑                  ↑              proved   sorry
   brd_tower_data    exists_cm_class            D3.2c
       ↑              _group_data              sorry
   ┌───┴───┐              ↑                  D3.2.tors
   ↓       ↓          CMTowerData              proved
gs_cm    chebotarev      ↑                  (via E10+E13)
_tower   _fixed_Q     SplitPrimeData
(sorry)  (sorry)         ↑
                    (chebotarev_fixed_Q)
                    or
                    (splitPrimeData_from_prime_list, proved Phase D2)
```

This diagram shows the dependency tree.  Sorried nodes (sorry) are leaves
that need Mathlib infrastructure.  Proved nodes (PROVED) are full Lean code.

## See also

- `assets/proof_outline.md` — 10-step proof walkthrough
- `assets/TUTORIAL.md` — newcomer tutorial
- `REPORT.md` — high-level status
- `CLAUDE.md` — agent-targeted comprehensive documentation
