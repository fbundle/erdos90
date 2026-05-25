# Dependency tree

## File imports

```
Main.lean
├── NumberField.lean
│   ├── NumberFieldDeep.lean (hub, re-exports all 5 below)
│   │   ├── NumberFieldDeep_Analytic.lean        (no Erdos90 imports)
│   │   ├── NumberFieldDeep_GSTower.lean
│   │   │   ├── NumberFieldDeep_Analytic.lean
│   │   │   ├── NumberFieldDeep_CM.lean
│   │   │   │   └── CMField/Basic.lean              (no Erdos90 imports)
│   │   │   └── CMField/CyclotomicSplitPrimes.lean
│   │   │       └── CMField/Basic.lean
│   │   ├── NumberFieldDeep_CM.lean
│   │   │   └── CMField/Basic.lean
│   │   ├── NumberFieldDeep_Assembly.lean
│   │   │   ├── NumberFieldDeep_GSTower.lean
│   │   │   └── NumberFieldDeep_CM.lean
│   │   └── NumberFieldDeep_ANT.lean
│   │       ├── NumberFieldDeep_GSTower.lean
│   │       └── NumberFieldDeep_CM.lean
│   ├── CosetAveraging.lean
│   │   └── Defs.lean
│   ├── DiscGeometry.lean
│   │   └── Defs.lean
│   └── Defs.lean
├── Geometric.lean
│   └── Defs.lean
├── Arithmetic.lean
│   └── Defs.lean
└── Defs.lean
```

## Theorem dependency chain

```
erdos_unit_distance_false  (Main.lean, THEOREM 1.1)
│   depends on: sorryAx (via the 2 sorries below)
│
├── admissible_family_to_planar_set  (Geometric.lean, PROVED)
│   └── exists_good_coset / lemma_2_4  (CosetAveraging.lean, PROVED)
│
└── exists_admissible_family  (NumberField.lean, PROVED modulo ↓)
    │
    ├── prop_p6  (NumberField.lean, PROVED — analytic)
    ├── hlog2_event  (NumberField.lean, PROVED — analytic)
    ├── lemma_2_4  (CosetAveraging.lean, PROVED — coset averaging)
    │
    └── prop_3_2_to_3_6_via_deep  (Assembly.lean, PROVED modulo ↓)
        │
        ├── golod_shafarevich_tower_with_lattice  (GSTower.lean)
        │   │   no additional sorries — assembly only
        │   │
        │   ├── gs_base_construction  (GSTower.lean, PROVED)
        │   │   D₀=1, rd_F=2ℓ, log bound via log_two_mul_le
        │   │
        │   └── gs_tower_levels → gs_tower_levels_proved  (GSTower.lean)
        │       ╔══════════════════════════════════════════════╗
        │       ║  S1: h_div_conj_mem_Λ   (line 355)          ║
        │       ║  S2: hClassNum          (line 364)          ║
        │       ╚══════════════════════════════════════════════╝
        │
        └── cm_norm_one_elements  (Assembly.lean, PROVED modulo S1,S2)
            │   class-group pigeonhole → norm-one set U
            │   uses cmData.h_classNumBound_zero (proved, rfl)
            │
            └── exists_cm_class_group_data  (CM.lean, PROVED)
                all fields proved (no sorries):
                ├── h_card_ratio    — uses cmData.hClassNum  (via S2)
                ├── hmk_unit_mem_Λ  — uses cmData.h_div_conj_mem_Λ (via S1)
                ├── hmk_unit_norm   — uses cmData.h_φ_norm_div_conj (proved)
                └── hmk_unit_inj    — count-based valuation (proved)
```

## The 2 sorries — what they block

Both in `gs_tower_levels_proved` (GSTower.lean), inside the `cmData : CMTowerData` literal.

| # | Field | Line | Statement | Why it's hard |
|---|-------|------|-----------|---------------|
| S1 | `h_div_conj_mem_Λ` | 355 | α/c(α) ∈ Λ = Φ(𝓞_K) | α/c(α) has val ∈ {−2,0,2} at split primes. −2 case needs Q²·(α/c(α)) ∈ 𝓞_K (Q = ∏ q_j). Current tower uses D₀=1 → Λ=Φ(𝓞_K), doesn't contain Φ(α/c(α)). Fix: compute Q from split primes, scale Λ. |
| S2 | `hClassNum` | 364 | h_K ≤ exp(0·f) = 1 | Placeholder classNumBound=0, so hClassNum asserts h_K ≤ 1. False for ℚ(ζ_p) with p ≥ 23 (Masley–Montgomery). Fix: quantitative Minkowski class-number bound, not in Mathlib v4.30. |

## Closure condition

```
golod_shafarevich_tower_with_lattice is proved
    ⟺ gs_tower_levels_proved is proved
    ⟺ S1 AND S2 are both closed
    ⟹ exists_admissible_family is proved
    ⟹ erdos_unit_distance_false is proved  (no more sorryAx)
```

## Proved (no sorry) — full list

- `gs_base_construction` — GS base D₀=1, rd_F=2ℓ
- `gs_tower_levels` / `gs_tower_levels_v2` — delegate to `gs_tower_levels_proved`
- `golod_shafarevich_tower_with_lattice` — assembly (structure correct, transitively sorried via S1,S2)
- `exists_fiber_ge_div` — pigeonhole lemma (§3)
- 4 CM lemmas (§4): `norm_div_star_eq_one`, `cm_norm_div_conj_eq_one`, `normAtPlace_mixedEmbedding_cm_div_conj_eq_one`, `mixedEmbedding_cm_div_conj_complex_norm_one`
- `mk_unit_from_cm_quotient` — infrastructure for mk_unit
- `exists_cm_class_group_data` — all CMClassGroupData fields proved (depends on CMTowerData sorried fields)
- `cm_norm_one_elements` — proved (takes h_div_conj_mem_Λ + hClassNum from CMTowerData)
- `prop_3_2_to_3_6_via_deep` — proved modulo S1,S2 (classNumBound_le_log_H closed via h_classNumBound_zero)
- `classNumBound_nonpos_iff_classNumber_one` (ClassNumBoundCounterexample.lean) — proved (not in main build)
- All geometric/combinatorial lemmas (Defs, DiscGeometry, CosetAveraging, Geometric)
- All CMField/Basic + CyclotomicSplitPrimes lemmas
- All analytic helpers (NumberFieldDeep_Analytic)
- All ANT lattice lemmas (NumberFieldDeep_ANT)
