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
   `golod_shafarevich_tower_with_lattice`).

3. **`NumberFieldDeep_CM.lean`** — §3–§5: Pigeonhole lemma (`exists_fiber_ge_div`,
   proved), CM field lemmas (proved), `CMClassGroupData` structure, and
   `exists_cm_class_group_data` (fully proved, including `hmk_unit_inj`; no sorries).

4. **`NumberFieldDeep_Assembly.lean`** — §6–§8: `cm_norm_one_elements` (proved),
   `prop_3_2_to_3_6_via_deep` (proved modulo the 2 GSTower sorries),
   `ERDOS_ANT_Postulates`, and `ant_postulates`.

5. **`NumberFieldDeep_ANT.lean`** — Sawin parameters (§Sawin), product formula
   separation (proved), integer separation (proved), Minkowski lattice transport
   (8 definitions/lemmas proved, `cmSeparation` now proved by correcting its
   statement to ∃ i and delegating to `cmSeparation_exists`), tower postulate
   (filled), `gs_tower_levels_v2` and `exists_cm_class_group_data_v2` (delegate
   to v1). All proved (no sorries).

The 2 remaining `sorry` statements (1 declaration, 1 actual `sorry` keyword warning),
blocking the main theorem via `sorryAx`:
- `h_div_conj_mem_Λ` within `gs_tower_levels_proved` (GSTower) — D₀ = Q² scaling
  needed so Φ(α/c(α)) ∈ Λ for α generating J_{ε₂}·J_{ε₁}⁻¹
- `classNumBound_nonpos` within `gs_tower_levels_proved` (GSTower) — requires
  log(h_K)/f ≤ 0, i.e., h_K ≤ 1 (restructure bound relative to log_H)

`gs_tower_levels` delegates to `gs_tower_levels_proved` (cyclotomic CM field ℚ(ζ_p)
with product-formula separation). `exists_cm_class_group_data` is fully proved
(including `hmk_unit_inj` via `FractionalIdeal.count` + `dec_trivial`).
`ant_postulates` (Assembly) delegates to `gs_tower_levels` + `exists_cm_class_group_data`
directly (no additional sorries).
-/
