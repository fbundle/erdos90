import Erdos90.NumberFieldDeep_Analytic
import Erdos90.NumberFieldDeep_GSTower
import Erdos90.NumberFieldDeep_CM
import Erdos90.NumberFieldDeep_Assembly
import Erdos90.NumberFieldDeep_ANT

/-!
# Deep Number-Theoretic Components

This file is an import hub that re-exports all deep number-theoretic components
from five specialized files:

1. **`NumberFieldDeep_Analytic.lean`** — §1: Analytic helpers (`log_two_mul_le`,
   `exp_sub_mul_eq_rpow_div_exp`, `card_ratio_ineq`), all proved.

2. **`NumberFieldDeep_GSTower.lean`** — §2: Golod–Shafarevich tower
   (`GSBaseData`, `gs_base_construction`, `gs_tower_levels` [proved via
   cyclotomic CM field ℚ(ζ_p)], `GSTowerData`,
   `golod_shafarevich_tower_with_lattice`).  One sorry: `h_div_conj_mem_Λ`
   (D₀ = Q² valuation scaling).

3. **`NumberFieldDeep_CM.lean`** — §3–§5: Pigeonhole lemma (`exists_fiber_ge_div`,
   proved), CM field lemmas (proved), `CMTowerData` structure (no longer has
   `classNumBound_nonpos`; removed in 2026-05-25 refactor), `CMClassGroupData`
   structure, and `exists_cm_class_group_data` (fully proved, including
   `hmk_unit_inj`; takes explicit `classNumBound_le_log_H` hypothesis, no sorries).

4. **`NumberFieldDeep_Assembly.lean`** — §6–§8: `cm_norm_one_elements` (proved,
   takes explicit `classNumBound_le_log_H`), `prop_3_2_to_3_6_via_deep` (proved
   modulo 2 sorries: `h_div_conj_mem_Λ` in GSTower and `classNumBound_le_log_H`
   at the call site), `ERDOS_ANT_Postulates`, and `ant_postulates`.

5. **`NumberFieldDeep_ANT.lean`** — Sawin parameters (§Sawin), product formula
   separation (proved), integer separation (proved), Minkowski lattice transport
   (8 definitions/lemmas proved, `cmSeparation` proved), tower postulate
   (filled), `gs_tower_levels_v2` and `exists_cm_class_group_data_v2` (delegate
   to v1). All proved (no sorries).

The 2 remaining `sorry` statements, blocking the main theorem via `sorryAx`:
- `h_div_conj_mem_Λ` within `gs_tower_levels_proved` (GSTower) — D₀ = Q² scaling
  needed so Φ(α/c(α)) ∈ Λ for α generating J_{ε₂}·J_{ε₁}⁻¹
- `classNumBound_le_log_H` within `prop_3_2_to_3_6_via_deep` (Assembly) —
  Minkowski class-number bound: log(h_K)/f ≤ log_H, i.e., h_K ≤ exp(log_H · f).
  This is mathematically TRUE (unlike the previous `classNumBound_nonpos : log(h_K)/f ≤ 0`
  which was false); requires the quantitative Minkowski bound not yet in Mathlib.

`gs_tower_levels` delegates to `gs_tower_levels_proved` (cyclotomic CM field ℚ(ζ_p)
with product-formula separation). `exists_cm_class_group_data` is fully proved
(including `hmk_unit_inj` via `FractionalIdeal.count` + `dec_trivial`).
`ant_postulates` (Assembly) delegates to `gs_tower_levels` + `exists_cm_class_group_data`
directly (no additional sorries).
-/
