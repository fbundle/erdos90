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
   (8 definitions/lemmas proved, `cmSeparation` now proved by correcting its
   statement to ∃ i and delegating to `cmSeparation_exists`), tower postulate
   (filled), `gs_tower_levels_v2` and `exists_cm_class_group_data_v2` (delegate
   to v1). 0 deep sorries remain in this file.

The 3 remaining `sorry` declarations (3 actual `sorry` keywords), all blocking
the main theorem via `sorryAx`:
- `hΛ_inj` within `gs_tower_levels` (GSTower) — first-coordinate injectivity;
  provably FALSE for placeholder ℤ[I]^f (counterexample: (0,I,0,…)); needs CM
  field Minkowski lattice from the Golod–Shafarevich tower (not in Mathlib v4.29.1)
- `hmk_unit_norm` within `exists_cm_class_group_data` (CM) — ‖0‖ = 0 ≠ 1;
  provably FALSE for placeholder mk_unit = 0; needs CM field + α/c(α) construction
- `hmk_unit_inj` within `exists_cm_class_group_data` (CM) — constant 0 not
  injective; provably FALSE with placeholder; needs split-prime valuation parity

`ant_postulates` (Assembly) delegates to `gs_tower_levels` + `exists_cm_class_group_data`
directly (no additional sorries).
-/
