# Search Results Index

Last updated: 2026-05-25

## New files added this session (May 25, 2026)

| File | Contents |
|------|---------|
| `openai_paper_prop2_2_construction.md` | Full construction from Prop 2.2 (pages 6-7): valuation formula, integrality, distinctness |
| `openai_paper_references.md` | Complete reference list + Appendix A propositions (A.11–A.13) with exact section citations |
| `mathlib_valuation_api.md` | Mathlib v4.30 adic valuation API: what exists vs. what's missing |
| `sawin_lemmas_6_9.md` | Sawin paper Lemmas 6–9: relative class number G_K, fiber bound, h^-(K) via Louboutin |
| `sorry_proof_strategy.md` | Proof strategy for all 3 sorries with missing Mathlib API list |
| `valuation_formula_derivation.md` | Step-by-step derivation of v_{𝔓_s}(u_ε) = 2(ε_s − η_s) + proof sketches |
| `class_number_bound_derivation.md` | Chain of bounds from rd(K_j) ≤ 2rd(F) to h(K_j) ≤ H_ℓ^{f_j} (Prop 3.7 + Minkowski) |
| `louboutin_wrong_file_note.md` | NOTE: assets/louboutin_2000_class_number.pdf is the wrong paper (complex analysis, not ANT) |

## Key findings from this session

### 1. The three sorries all reduce to one missing Mathlib lemma

The **conjugation-swapping valuation** lemma is the core gap:
```lean
-- NOT in Mathlib v4.30.0-rc2
-- [Neukirch, Algebraic Number Theory, I.8.5]
lemma conjIdeal_valuation_swap (𝔓 : HeightOneSpectrum (𝓞 K)) (α : K) :
    v_{c𝔓}(c(α)) = v_{𝔓}(α)
```
Once this is available, all three sorries close by straightforward computation.

### 2. The exact valuation formula (paper equation (4))

```
v_{𝔓_s}(u_ε) = 2(ε_s − η_s)   where u_ε = α_ε / c(α_ε)
v_{c𝔓_s}(u_ε) = −2(ε_s − η_s)
```
Proof:
- v_{𝔓_s}(α_ε) = ε_s − η_s (from ideal equation (α_ε) = 𝔄_ε · 𝔄_η^{-1})
- v_{𝔓_s}(c(α_ε)) = v_{c𝔓_s}(α_ε) = −(ε_s − η_s) (conjugation swaps)
- v_{𝔓_s}(u_ε) = (ε_s−η_s) − (−(ε_s−η_s)) = 2(ε_s−η_s)

### 3. Mathlib APIs confirmed available

- `IsDedekindDomain.HeightOneSpectrum.valuation K : Valuation K ℤᵐ⁰` (AdicValuation.lean:298)
- `intValuation.map_mul'` — multiplicativity of v-adic valuation (AdicValuation.lean:111)
- `intValuationDef_if_neg` — formula in terms of Associates.count (AdicValuation.lean:94)
- `ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring` — class equality ↔ principal (ClassGroup.lean:267)
- `IsCMField.complexConj` — complex conjugation (CMField.lean:143)
- `maximalRealSubfield` — K⁺ subfield (TotallyRealComplex.lean:125)

### 4. Class number bound (for `h_card_ratio`)

Paper Proposition 3.7: h(K) ≤ max{2, rd(K)}^{C_class·[K:ℚ]}. 
References: [Neu99, Chapter I, Section 5] and [Lan94, Chapter V].
- NOT in Mathlib
- The `log_H` parameter in `exists_cm_class_group_data` is supposed to encode this bound
- Most pragmatic fix: add `h_class_bound : Fintype.card (ClassGroup (𝓞 K)) ≤ ⌈Real.exp (log_H * f)⌉₊` as an explicit hypothesis, supplied by the GS tower

### 5. Wrong file note

`assets/louboutin_2000_class_number.pdf` is actually a paper on plurisubharmonic functions by Lelong-Rashkovskii (arXiv:math/9901014). The actual Louboutin ANT class number paper (cited by Sawin) is not in assets.

---

## Existing search results (from previous sessions)

| File | Contents |
|------|---------|
| `mathlib_cm_ideal_api.md` | CM field + ClassGroup + Ramification API survey |
| `mathlib_class_group.md` | ClassGroup definitions |
| `mathlib_class_number.md` | classNumber and bounds |
| `mathlib_dedekind_ideal.md` | Dedekind domain ideal API |
| `mathlib_discriminant.md` | Discriminant lemmas |
| `mathlib_gs_chebotarev_api.md` | GS tower and Chebotarev APIs |
| `mathlib_cm_field.md` | IsCMField API |
| `mathlib_canonical_embedding.md` | mixedEmbedding and lattice basis |
| `sawin_section2_construction.md` | Sawin §2 construction (prior session) |
| `proof_synthesis.md` | Earlier proof strategy notes |
| `milne_cm_notes.md` | Milne CM notes summary |
| `sawin_2605_20579.bbl` | Sawin paper bibliography |
| `sawin_2605_20579.tex` | Sawin paper LaTeX source |
| Various arxiv/wikipedia entries | Background references |

---

## Key textbook references (from OpenAI paper appendix)

| Tag | Book | Chapters relevant to proof |
|-----|------|---------------------------|
| [Neu99] | Neukirch, *Algebraic Number Theory* (1999) | I.4 (valuations), I.5 (Minkowski bound), I.8 (Galois acts on primes), VII.13 (Chebotarev) |
| [Lan94] | Lang, *Algebraic Number Theory* (1994) | V (class number bounds) |
| [Was97] | Washington, *Introduction to Cyclotomic Fields* (1997) | 3 (cyclotomic class field theory) |
| [NSW08] | Neukirch-Schmidt-Wingberg, *Cohomology of Number Fields* (2008) | X.10 (Shafarevich relation-rank) |
| [Koc02] | Koch, *Galois Theory of p-Extensions* (2002) | 4 (Frattini), 11 (GS inequality) |
