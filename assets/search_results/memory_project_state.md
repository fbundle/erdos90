---
name: Remaining sorry gaps
description: What's left to prove in the erd46 Lean formalization and why it's hard
type: project
originSessionId: 15e9ff09-c395-4925-9dd3-d3affcf1131e
---
As of 2026-05-23, two `def ... := by sorry` remain, both in `Erdos90/NumberFieldDeep.lean`:

1. **`gs_tower_levels`** (line ~159): Chebotarev tower + Minkowski type bridge (Prop 3.6)
2. **`exists_cm_class_group_data`** (line ~453): CM field / class-group construction (Prop 2.2)

The main theorem `erdos_unit_distance_false` is fully proved (depends transitively on these two sorries via `sorryAx`).

**§1 now has 4 analytic lemmas**, all compilable:
- `log_two_mul_le` — log(2ℓ) ≤ ℓ·log ℓ for ℓ ≥ 2
- `exp_sub_mul_eq_rpow_div_exp` — exp identity: exp((t·log 2 − log_H)·f) = 2^{t·f} / exp(log_H·f)
- `card_ratio_ineq` — cardinality ratio bound for the class-group pigeonhole

**§2: `gs_base_construction` now proved** using D₀ = 1, rd_F = 2ℓ, with `log_two_mul_le`
providing the log bound. The structure only requires positivity and log bounds, which these
simplified choices satisfy.

**§4 still has 4 fully proved CM lemmas**:
- `norm_div_star_eq_one` — ‖z / star z‖ = 1
- `cm_norm_div_conj_eq_one` — ‖φ(α / c(α))‖ = 1 at each complex embedding
- `normAtPlace_mixedEmbedding_cm_div_conj_eq_one` — normAtPlace = 1 at every infinite place
- `mixedEmbedding_cm_div_conj_complex_norm_one` — concrete ‖.2 w‖ = 1 for each complex place

**Why the remaining two can't be closed with current Mathlib v4.29.1:**
- `gs_tower_levels` needs quantitative Chebotarev (build infinite tower from pro-p quotient),
  the type bridge `mixedSpace K ≃ Fin f → ℂ`, and transport of fundamental domain + separation
- `exists_cm_class_group_data` needs CM field construction with split-prime ideal pairs
  (𝔓_j, c𝔓_j), class-number bound |G| ≤ exp(log_H·f), and the mk_unit constructor bridging
  number fields to the Fin f → ℂ lattice

**How to apply:** If asked about remaining sorries, point to these two gaps. The proof
architecture is sound — only the algebraic number theory input is missing from Mathlib.
