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
   (`GSBaseData`, `gs_base_construction`, `gs_tower_levels` [sorried],
   `GSTowerData`, `golod_shafarevich_tower_with_lattice`).

3. **`NumberFieldDeep_CM.lean`** — §3–§5: Pigeonhole lemma (`exists_fiber_ge_div`,
   proved), CM field lemmas (proved), `CMClassGroupData` structure, and
   `exists_cm_class_group_data` (sorried).

4. **`NumberFieldDeep_Assembly.lean`** — §6–§8: `cm_norm_one_elements` (proved
   modulo §5), `prop_3_2_to_3_6_via_deep` (proved modulo §2+§5),
   `ERDOS_ANT_Postulates`, and `ant_postulates` (bundles the two sorries).

5. **`NumberFieldDeep_ANT.lean`** — Sawin parameters (§Sawin), product formula
   separation (proved), integer separation (proved), Minkowski lattice transport
   (7 definitions/lemmas proved, `cmSeparation` sorried), tower postulate
   (filled), `gs_tower_levels_v2` and `exists_cm_class_group_data_v2` (delegate
   to v1). 1 deep sorry remains (`cmSeparation`).

The 3 remaining `sorry` declarations (4 actual `sorry` keywords):
- `hΛ_sep` within `gs_tower_levels` (GSTower) — first-coordinate separation;
  placeholder lattice ℤ[I]^f violates the property
- `hmk_unit_norm` + `hmk_unit_inj` within `exists_cm_class_group_data` (CM) —
  α/c(α) norm-1 + injectivity on fibers; both need CM field construction
- `cmSeparation` (ANT) — same gap as `hΛ_sep`, applied to transported Minkowski lattice

`ant_postulates` (Assembly) delegates to `gs_tower_levels` + `exists_cm_class_group_data`
directly (no additional sorries).
-/
