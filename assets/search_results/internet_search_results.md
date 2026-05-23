# Internet Search Results — May 2026

Searches performed by background agents (2026-05-23).

---

## 1. Chebotarev Density Theorem in Lean4/Mathlib

**Status: NOT in Mathlib v4.29.1**

- No Mathlib page or PR for Chebotarev density theorem found.
- Frobenius elements in global number fields not in Mathlib.
- `Mathlib/NumberTheory/FrobeniusNumber.lean` is the Frobenius coin problem (unrelated).
- `Mathlib/RingTheory/Frobenius.lean` covers Frobenius endomorphisms in positive characteristic.
- No decomposition/inertia groups in global Galois groups formalized.

Confirmed by: 2022 Zulip thread (David Loeffler) stating Frobenius elements and global Galois groups are missing. No evidence of subsequent merged PR as of May 2026.

The arxiv paper 2508.09480 is "An effective version of Chebotarev's density theorem" by Das–Kadiri–Ng (2025) — a *mathematical* paper used as a reference in the unit-distance proof, NOT a Lean formalization.

---

## 2. Golod–Shafarevich Theorem Formalization

**Status: NOT in Lean4/Mathlib**

No Lean4/Mathlib formalization of:
- Golod–Shafarevich inequality (r > d²/4 for finite nontrivial pro-p groups)
- Shafarevich relation-rank estimate for Galois groups of unramified extensions
- Pro-p group theory (Frattini subgroup, d(G), r(G) in the profinite sense)

The CMI HIMR Summer School (Oxford, July 2025) on Formalizing Class Field Theory covered Hilbert 90 and local class field theory but not GS tower theory.

---

## 3. IsCMField API — What IS in Mathlib

The `IsCMField` class IS in Mathlib:
```
File: Mathlib/NumberTheory/NumberField/CMField.lean
class IsCMField (K : Type*) [Field K] [CharZero K] : Prop
  to_isTotallyComplex : IsTotallyComplex K
  is_quadratic : IsQuadraticExtension (maximalRealSubfield K) K
```

Key theorems available:
- `complexConj K : K ≃ₐ[K⁺] K` (the CM involution)
- `complexEmbedding_complexConj : φ(complexConj K x) = conj(φ x)`
- `complexConj_eq_self_iff : complexConj K x = x ↔ x ∈ K⁺`
- `ringOfIntegersComplexConj : (𝓞 K) ≃ₐ[𝓞 K⁺] (𝓞 K)`
- `unitsMulComplexConjInv : (𝓞 K)ˣ →* torsion K` (map u ↦ u·(c(u))⁻¹)
- `IsCyclotomicExtension.isCMField` (cyclotomic extensions are CM)

**NOT in Mathlib**: split-prime API for CM fields, norm-1 element bounds, class number via root discriminant.

---

## 4. Type Bridge mixedSpace K → Fin f → ℂ

**Status: NOT a standalone theorem in Mathlib**

For totally complex K of degree 2f:
- `mixedSpace K = (∅ → ℝ) × ({w : IsComplex w} → ℂ)` (real part empty)
- `nrComplexPlaces K = f`
- Bridge requires: `Fintype.equivFin {w : IsComplex w}` + `LinearEquiv.piCongrLeft`

The tools exist individually but no single theorem provides the bridge. Must construct manually:
```lean
-- not yet done in erd46 or Mathlib
```

---

## 5. Class Number Bounds

### In Mathlib:
- `exists_ideal_in_class_of_norm_le` — Minkowski bound: every class has ideal of norm ≤ M K
- M K = (4/π)^r₂ · (n!/n^n) · √|discr K|
- `classNumber K = Fintype.card (ClassGroup (𝓞 K))` — finiteness
- `volume_fundamentalDomain_latticeBasis` — (2⁻¹)^r₂ · √‖discr K‖₊

### NOT in Mathlib (but available in mathematical literature):
**Louboutin's bound** (used in arXiv:2605.20579 Lemma 9):
```
h⁻(K) ≤ 8 · rd_{K/F}² · (√rd_{K/F} · log(rd_{K/F}) · e/(4π))^f
```
For K = F(i) from the GS tower with rd_{K/F} = √(4·∏ q_b) bounded by a constant, this gives h(K) ≤ C^f.

**Simple bound for large-degree fields** (used in remarks paper arXiv:2605.20695):
h(K) ≤ |disc(K)|  [for [K:ℚ] ≥ 4, by Borel-Prasad]

**Minkowski's theorem** (gives h(K) ≤ M_K, computable from Mathlib's exists_ideal_in_class_of_norm_le):
h(K) ≤ (4/π)^f · (2f)!/(2f)^{2f} · √|disc(K)|  ≤ C^f · rd(K)^f

---

## 6. Related Papers Found

### arXiv:2605.20695 — "Remarks on the Disproof of the Unit Distance Conjecture"
- URL: https://arxiv.org/html/2605.20695v1
- Authors: Alon, Bloom, Gowers, Litt, Sawin et al.
- Contains: more detailed mathematical commentary on the OpenAI proof
- Key fact: confirms that α/c(α) has norm 1 everywhere (Lemma 2.2)
- States class number bound h(K) ≤ |disc(K)| for [K:ℚ] ≥ 4

### arXiv:2605.20579 — "An explicit lower bound for the unit distance problem" (Sawin)
- URL: https://arxiv.org/html/2605.20579v1
- Achieves explicit δ = 0.014114 (i.e., ν(n) ≥ n^{1.014114})
- Contains: detailed lemmas 1-12 for the construction
- Lemma 9 (Louboutin bound for h⁻(K)), Lemma 11 (GS criterion), Lemma 12 (tower)
- Most explicit version of the construction; good reference for formalizing the sorries

### arXiv:2507.10387 — "Effective equidistribution of norm one elements in CM-fields"
- URL: https://arxiv.org/pdf/2507.10387
- By Akhtari–Vaaler–Widmer
- Directly relevant: studies elements of the form α/c(α) in CM fields
- Confirms |σ(α/c(α))| = 1 for all complex embeddings σ
- "Elements of the form α/c(α) where c is complex conjugation have norm one by construction"

### Harvard thesis: "The Golod-Shafarevich Theorem and the Class Field Tower Problem" (Zhou)
- URL: https://people.math.harvard.edu/theses/senior/zhou/zhou.pdf
- Self-contained exposition of GS theory and infinite class field towers
- Useful for understanding the mathematical content of gs_tower_levels sorry

### arXiv:2406.00797 — "Infinite class field tower with small root discriminant"
- URL: https://arxiv.org/pdf/2406.00797
- More recent version of the Hajir-Maire-Ramakrishna tower results
- Shows existence of infinite towers with small (bounded) root discriminant

### Lagarias–Odlyzko (typeset) — "Effective Versions of the Chebotarev Density Theorem"
- URL: https://aareyanmanzoor.github.io/assets/articles/lagarias-odlyzko.pdf
- Original 1977 paper on effective Chebotarev, used for Prop 3.6 of OpenAI proof
- Main theorem: π_C(x, L/K) = (|C|/|G|) Li(x) + O(x^{1/2} log(d_L x^{n_L})) [GRH]

---

## 7. Status of the erd46 Lean Formalization (this project)

This project (erd46) is the ONLY known Lean4 formalization of the OpenAI unit-distance result. It has:
- Main theorem `erdos_unit_distance_false` proved (uses 2 sorries)
- All geometric and analytic lemmas proved
- 2 remaining sorries in `NumberFieldDeep.lean`:
  - `gs_tower_levels` (Prop 3.6 + type bridge) — requires GS + Chebotarev
  - `exists_cm_class_group_data` (Prop 2.2) — requires CM field + split primes + class number bound

No other Lean4 formalization attempt was found.

---

## 8. Mathlib Development That Would Help

Currently missing from Mathlib:
1. **Chebotarev density theorem** — most important gap
2. **Frobenius elements in global number fields** — needed for Chebotarev
3. **Pro-p group theory** — Golod-Shafarevich inequality (r > d²/4), Frattini subgroup
4. **Split-prime API for CM fields** — (𝔓, c𝔓) pairs when p splits in K
5. **Class number bound from root discriminant** — h(K) ≤ C(rd(K))^f
6. **Type bridge** — mixedSpace K ≃ Fin f → ℂ for totally complex K
