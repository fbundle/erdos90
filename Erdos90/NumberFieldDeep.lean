import Erdos90.NumberFieldDeep_Analytic
import Erdos90.NumberFieldDeep_GSTower
import Erdos90.NumberFieldDeep_CM
import Erdos90.NumberFieldDeep_Assembly

/-!
# Deep Number-Theoretic Components

This file is an import hub that re-exports all deep number-theoretic components
from four specialized files:

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

The two remaining `sorry` gaps in the formalization are:
- `gs_tower_levels` (Chebotarev + Minkowski type bridge)
- `exists_cm_class_group_data` (CM field / class-group construction)
-/
