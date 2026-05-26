/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/

/-!
# Class Field Theory infrastructure — Index

This file is **documentation-only**.  It serves as the master index for the
class-field-theory-adjacent infrastructure files in `Erdos90/Mathlib4_Extra/`.

## File map

### Discriminant + ramification (PROVED foundations)

| File | What |
|---|---|
| `UnramifiedDiscriminant.lean` | **PROVED**: `rootDiscr` invariant under everywhere-unramified extensions.  Uses Mathlib's `differentIdeal` + `not_dvd_differentIdeal_iff` (proved).  No sorry. |
| `TameRamification.lean` | Tame ramification predicate (stub) + HMR's refined discriminant formula (postulated).  Documents the connection to `UnramifiedDiscriminant.lean`. |

### Class field theory (HCF stub + concrete instances)

| File | What |
|---|---|
| `ClassFieldTheory.lean` | **Main file**.  `HilbertClassFieldExt K` structure with Galois + Artin reciprocity isomorphism.  PROVED corollaries: `rootDiscr_hcf_eq`, `card_gal_hcf_eq_classNumber`, `finiteDimensional`, `isTotallyComplex`, `bijective_algebraMap_of_classNumber_one`.  **FULLY PROVED instances**: `identity`, `rat`, `cyclotomic_three`, `cyclotomic_five` (for class-number-1 fields).  POSTULATES: `hilbertClassField_exists`, `isCMField_postulate`, `hilbert_principal_ideal_postulate`, `hilbertPClassField_exists`. |
| `RayClassField.lean` | `MaxProPExt K p S` (HMR's `K_S^{(p)}`) + `RayClassField K 𝔪` stubs.  The S-restricted analog used in HMR's refined GS construction. |
| `Conductor.lean` | `Conductor K L` structure for the conductor of an abelian extension.  Documents the conductor-discriminant formula. |

### Local + global CFT framework

| File | What |
|---|---|
| `LocalCFT.lean` | Local Artin map for local fields (stub).  Frutos-Fernández's external library has partial Lean formalization. |
| `GlobalCFT.lean` | Global Artin map + idele group + idele class group (stubs).  Documents factorization through HCF for the simpler case. |

### Analytic CFT

| File | What |
|---|---|
| `HeckeCharacters.lean` | Hecke characters + Hecke L-functions (stubs).  Architectural bridge to Chebotarev density. |
| `BrauerGroup.lean` | Brauer group + Hasse-Brauer-Noether (stubs).  Cohomological CFT. |

### Density theorems (analytic input for HMR)

| File | What |
|---|---|
| `Chebotarev.lean` | Chebotarev density + Ihara's theorem (stubs).  The analytic input for `chebotarev_fixed_Q` (which is still on the proof path). |

### Golod–Shafarevich (the other half of HMR)

| File | What |
|---|---|
| `GolodShafarevich.lean` | `GolodShafarevich.Input` + GS infinite tower postulate + `gs_unramified_tower_with_bounded_rd` (PROVED bridge).  This is the file that powers `gs_cm_tower` (Phase E14). |

### Deep CFT theory (off-path infrastructure)

| File | What |
|---|---|
| `Iwasawa.lean` | Cyclotomic `ℤ_p`-extension + Iwasawa invariants (μ, λ, ν) + Ferrero–Washington μ=0 postulate.  The deeper framework around HMR-style towers. |
| `ReciprocityLaws.lean` | Cubic + biquadratic reciprocity stubs.  Documents the CFT context for splitting-prime calculations. |

## Dependency graph

```
                  Erd46 proof of unit-distance theorem
                                 ↑
                                gs_cm_tower (PROVED via Phase E14)
                                 ↑
                       GolodShafarevich.gs_unramified_tower_with_bounded_rd (PROVED)
                                 ↑
              gs_cm_tower_infinite_postulate (SORRY — the labelled postulate)
                                 │
                                 ▼
                    Need: HMR construction = GS + CFT
                       ┌──────────────────────┴──────────────────────┐
                       ▼                                              ▼
              Golod–Shafarevich inequality                Class field theory
              (group cohomology)                         (Artin reciprocity)
                  │                                              │
                  ▼                                              ▼
         GolodShafarevich.lean                  ClassFieldTheory.lean
         (GS Input + criterion stub)            (HCF + Artin reciprocity)
                                                       │
                                                       ▼
                                        RayClassField.lean (S-restricted)
                                                       │
                                                       ▼
                                  TameRamification.lean (rd bound)
                                                       │
                                                       ▼
                                  UnramifiedDiscriminant.lean (PROVED)
```

## Status summary

**PROVED Lean (no sorry)**:
- `UnramifiedDiscriminant.lean`: full module, ~120 LOC.
- `ClassFieldTheory.lean`: ~7 corollaries + 1 fully-proved instance + 3 concrete cases.

**Labelled postulates** (each one a clear Mathlib-PR target):
- `hilbertClassField_exists` (Artin reciprocity for HCF)
- `hilbertPClassField_exists` (`p`-HCF existence)
- `maxProPExt_exists` (max pro-p extension)
- `gs_cm_tower_infinite_postulate` (GS + HMR combined)
- `chebotarev_density_postulate`, `ihara_split_primes_postulate`
- `localArtinMap_postulate`, `globalArtinMap_postulate`
- `discr_formula_tame_postulate`, `rd_bounded_in_tame_tower_postulate`
- `hilbert_principal_ideal_postulate` (Hilbert 94)
- `isCMField_postulate` (CM preservation)
- `heckeLFunction_postulate`, `hecke_L_non_vanishing_at_one_postulate`
- `hasseBrauerNoether_postulate`

**Closing roadmap**: see `assets/search_results/closing_roadmap.md` for the 5-PR
Mathlib strategy to bring the postulates into Mathlib core.

This infrastructure makes the Erd46 project's class-field-theory dependencies
**fully legible** as a small number of clearly-stated, individually-citable
postulates, each in its own Mathlib-PR-ready file.
-/
