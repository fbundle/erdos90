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
   (`cmMinkowskiEquiv` proved, `cmTransportedBasis`, `cmMinkowskiLattice`,
   `cmFundamentalDomain`, and 3 properties proved; `cmSeparation` sorried),
   tower postulate `sawin_tower_exists` (1 sorry), `gs_tower_levels_v2` and
   `exists_cm_class_group_data_v2` (delegate to v1). 2 deep sorries remain.

The remaining `sorry` gaps (7 total across 5 declarations):
- `hΛ_sep` within `gs_tower_levels` (GSTower) — first-coordinate separation
- `hmk_unit_norm` + `hmk_unit_inj` within `exists_cm_class_group_data` (CM) — α/c(α) construction
- `ant_postulates` (Assembly, 2 sorries) — bundles the above
- `cmSeparation` (ANT) — embedding reordering for first-coordinate separation
- `sawin_tower_exists` (ANT) — GS + Chebotarev tower postulate
-/
