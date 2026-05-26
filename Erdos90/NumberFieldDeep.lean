import Erdos90.NumberFieldDeep_Analytic
import Erdos90.NumberFieldDeep_GSTower
import Erdos90.NumberFieldDeep_CM
import Erdos90.NumberFieldDeep_Assembly
import Erdos90.NumberFieldDeep_ANT

/-!
# Deep Number-Theoretic Components

This file is an import hub that re-exports all deep number-theoretic components
from five specialized files:

1. **`NumberFieldDeep_Analytic.lean`** — §1: Analytic helpers
   (`log_two_mul_le`, `exp_sub_mul_eq_rpow_div_exp`, `card_ratio_ineq`),
   all proved.

2. **`NumberFieldDeep_GSTower.lean`** — §2: Golod–Shafarevich tower.
   - `BRDTowerData ℓ` structure + `brd_tower_data ℓ hℓ : BRDTowerData ℓ`
     proved Lean code modulo two literature gaps: `gs_cm_tower` (HMR 2021
     GS+CM lift) and `chebotarev_fixed_Q` (HMR theo:ihara).
   - `class_num_bound_of_brd` PROVED Lean code (Phase E9 chain assembly)
     modulo three off-path sorries in `Mathlib4_Extra/ClassNumberBound.lean`.
   - `brd_cm_tower_postulate` PROVED Lean code assembling the lattice +
     `CMTowerData`.

3. **`NumberFieldDeep_CM.lean`** — §3–§5: Pigeonhole lemma
   (`exists_fiber_ge_div`, proved), CM lemmas (proved), `CMTowerData`
   structure with fixed `t'_param`/`spData`, `CMClassGroupData` +
   `exists_cm_class_group_data` (fully proved, takes `ht'_ge_t_plus_one`
   and `classNumBound_le_log_H` as hypotheses).

4. **`NumberFieldDeep_Assembly.lean`** — §6–§8: `cm_norm_one_elements`
   (proved), `prop_3_2_to_3_6_via_deep` (assembly theorem, proved
   modulo the sorries listed below), `ERDOS_ANT_Postulates`, `ant_postulates`.

5. **`NumberFieldDeep_ANT.lean`** — Sawin parameters, product formula
   separation, integer separation, Minkowski lattice machinery
   (`cmMinkowskiEquiv`, `cmFundamentalDomain`, etc., all proved or
   delegating to `CMField/MinkowskiLattice.lean`), `gs_tower_levels_v2`,
   `exists_cm_class_group_data_v2`.  No sorries in this file.

## Current sorries on the proof path

Two literature gaps:
- `gs_cm_tower` (GSTower) — HMR 2021 GS-tower existence + CM lift
- `chebotarev_fixed_Q` (GSTower) — HMR theo:ihara (fixed split primes
  across the tower via effective Chebotarev)

Both require Mathlib infrastructure not yet present (class field theory,
Chebotarev density, L-function continuation).

## Off-path infrastructure sorries

Three Mathlib-PR-shaped sorries in `Mathlib4_Extra/ClassNumberBound.lean`:
- `regulator_lower_bound_cm` (Friedman 1989)
- `dedekind_residue_upper_bound_cm` (Louboutin 2000)

Both blocked on Mathlib's `dedekindZeta` functional equation.

See `REPORT.md` for the high-level human-readable progress log and
`assets/search_results/closing_roadmap.md` for the 5-PR Mathlib strategy.
-/
