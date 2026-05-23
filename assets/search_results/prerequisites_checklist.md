# Prerequisites Checklist for the Two Remaining Sorries

This checklist maps every mathematical prerequisite to its Lean status.

---

## Sorry 1: `gs_tower_levels` — Prop 3.6 + Minkowski type bridge

Goal: `∃ f ≥ M, ∃ hf1 Λ (Countable Λ) F, IsAddFundamentalDomain Λ F vol ∧ vol F < ∞ ∧ ∀ v ∈ Λ, v ≠ 0 → ‖v(fin0)‖ ≥ D₀⁻¹`

### Pre-1: Choose ℓ primes rᵢ ≡ 1 (mod 3)
- **Math**: Dirichlet's theorem guarantees infinitely many such primes.
- **Lean**: `Nat.setOf_prime_infinite` + primes in APs not constructively given. Dirichlet not in Mathlib for general moduli.
- **Status**: ❌ Not directly available (Dirichlet's theorem for AP not in Mathlib; only PNT for ℤ)

### Pre-2: Cyclic cubic subfield L_i of ℚ(ζ_{rᵢ})
- **Math**: ℚ(ζ_r)/ℚ is cyclic of degree r-1. Its unique cyclic cubic subfield (if 3 | r-1) corresponds to the kernel of (ℤ/rℤ)× → ℤ/3ℤ.
- **Lean**: `IsCyclotomicExtension.isGalois` gives Galois structure. Subfields via `IntermediateField`. But constructing the specific cubic subfield requires class field theory / character maps.
- **Status**: ❌ Not directly available (no cubic subfield construction from cyclotomic in Mathlib)

### Pre-3: Conductor-discriminant formula |D_F| = D² for the composite field F
- **Math**: For abelian F/ℚ with characters χ₁,...,χₗ: |D_F| = ∏ f(χᵢ) where f(χᵢ) = rᵢ.
- **Lean**: No conductor-discriminant formula in Mathlib.
- **Status**: ❌ Not available

### Pre-4: M/F everywhere unramified (Prop 3.2)
- **Math**: Conductor-discriminant gives |D_M| = |D_F|^{[M:F]} · N_{F/ℚ}(𝔡_{M/F}). Equality |D_M| = |D_F|^{[M:F]} forces 𝔡_{M/F} = 𝒪_F, i.e., M/F unramified.
- **Lean**: No theorem connecting conductor-discriminant to unramifiedness in this way.
- **Status**: ❌ Not available

### Pre-5: d(G) ≥ ℓ-1 for G = Gal(F^{ur,3}/F)
- **Math**: Since M/F is abelian unramified with Galois group (ℤ/3ℤ)^{ℓ-1}, and G is the maximal pro-3 extension, G surjects onto (ℤ/3ℤ)^{ℓ-1}, so d(G) ≥ ℓ-1.
- **Lean**: Profinite groups in Mathlib (`Galois/Profinite.lean`) but no `d(G)` function (minimal generators of pro-p group) formalized.
- **Status**: ❌ Not available

### Pre-6: Shafarevich's relation-rank estimate r(G) ≤ d(G) + C₀ (Prop 3.5)
- **Math**: For totally real cubic F with ζ₃ ∉ F and G = Gal(F^{ur,3}/F): r(G) ≤ d(G) + C₀.
- **Lean**: Not in Mathlib. Requires pro-p cohomology (H²) theory for number fields.
- **Status**: ❌ Not available

### Pre-7: Golod–Shafarevich inequality (Prop 3.4)
- **Math**: If pro-p group G has r(G) ≤ d(G)²/4, then G is infinite.
- **Lean**: Not in Mathlib. Koch's "Galois Theory of p-Extensions" Ch. 11.
- **Status**: ❌ Not available

### Pre-8: Chebotarev — choose q_b with Frobenius in Φ(G) (Prop 3.6)
- **Math**: Chebotarev density theorem for the Frattini-quotient extension E/ℚ gives rational primes with prescribed Frobenius class.
- **Lean**: Chebotarev NOT in Mathlib. No Frobenius elements in global number fields.
- **Status**: ❌ Not available

### Pre-9: G̅ = G/N is infinite (from GS applied to G̅)
- **Math**: After killing Frobenius above q_b's, d(G̅) = d, r(G̅) ≤ d + C₀ + 3t ≤ d²/4 for large d. GS gives G̅ infinite.
- **Lean**: Requires Pre-6 + Pre-7 + Pro-3 group theory.
- **Status**: ❌ Not available (depends on all above)

### Pre-10: Infinite tower F = F₀ ⊂ F₁ ⊂ ... with f_j → ∞
- **Math**: From G̅ infinite, take a descending chain of open normal subgroups with indices → ∞. Fixed fields give the tower.
- **Lean**: `Galois/Infinite.lean` has `IntermediateFieldEquivClosedSubgroup` but no "descending chain of open subgroups with indices → ∞" theorem for infinite pro-p groups.
- **Status**: ❌ Not available

### Pre-11: K_j = F_j(i) is a CM field with [K_j:ℚ] = 2f_j
- **Math**: F_j totally real → K_j = F_j(i) totally imaginary quadratic extension of F_j.
- **Lean**: `IsCMField` exists; for K = F(i) with F totally real: `isTotallyComplex_of_algebra` and the CM structure. The degree [K_j:ℚ] = 2f_j follows from [F_j(i):F_j] = 2.
- **Status**: ⚠️ Partially available (given F_j, can deduce CM structure; but F_j not constructed)

### Pre-12: Type bridge mixedSpace K_j → Fin f_j → ℂ
- **Math**: For totally complex K of degree 2f, nrComplexPlaces = f, so mixedSpace K ≅ Fin f → ℂ.
- **Lean**: Build from `IsTotallyComplex.nrRealPlaces_eq_zero`, `Fintype.equivFin`, `LinearEquiv.piCongrLeft`.
- **Status**: ⚠️ Buildable (tools exist, not assembled into one lemma)

### Pre-13: IsAddFundamentalDomain Λ F volume (after type bridge)
- **Math**: `fundamentalDomain_integerLattice` for K_j, then transport across bridge.
- **Lean**: `fundamentalDomain_integerLattice` exists in Mathlib; transport needs `IsAddFundamentalDomain.vadd_set` or volume-preserving map.
- **Status**: ⚠️ Mostly available (transport lemma may need to be proved)

### Pre-14: volume F < ∞
- **Math**: volume = (2⁻¹)^f · √|discr K_j| which is finite.
- **Lean**: `volume_fundamentalDomain_latticeBasis` gives finite ENNReal value.
- **Status**: ✅ Available in Mathlib

### Pre-15: First-coordinate separation ‖v(fin0)‖ ≥ D₀⁻¹
- **Math**: For 0 ≠ v ∈ Λ, product formula gives ∏|σ_r(v)| ≥ D₀^{-f}, so max_r ≥ D₀⁻¹. But need FIRST coordinate specifically.
- **Lean**: Need to argue that for the chosen labeling of embeddings, σ₁ achieves the bound. Not straightforward without re-ordering.
- **Status**: ❌ Not directly available (requires careful argument about which coordinate)

---

## Sorry 2: `exists_cm_class_group_data` — Prop 2.2

Goal: Fill all fields of `CMClassGroupData f t log_H Λ`

### Pre-A: CM field K with [K:ℚ] = 2f, IsCMField K, NumberField K
- **Math**: K = K_j from the GS tower.
- **Lean**: Depends on Pre-1 through Pre-11 above.
- **Status**: ❌ Not available without gs_tower_levels

### Pre-B: Split prime ideal pairs {𝔓_s, c𝔓_s} for s = 1,...,m=tf
- **Math**: Each q_b splits completely in F_j (from Chebotarev construction), giving f primes of F_j above q_b, each splitting into a pair in K_j. So t·f pairs total.
- **Lean**: No split-prime API for CM fields. Need: "if q splits in F and q ≡ 1 mod 4, then each prime of F above q splits in K = F(i)".
- **Status**: ❌ Not available

### Pre-C: E = {0,1}^m as a Fintype
- **Math**: E = {0,1}^m ≅ Fin 2 × ... × Fin 2 (m times).
- **Lean**: `Fin 2 → Fin m → Bool` or `Fin (2^m)` or `Finset.pi`. Standard Lean types.
- **Status**: ✅ Available in Lean

### Pre-D: G = ClassGroup (𝓞 K), Fintype G
- **Math**: ClassGroup of any number field is finite.
- **Lean**: `instFintypeClassGroup : Fintype (ClassGroup (𝓞 K))` is in Mathlib.
- **Status**: ✅ Available (given K)

### Pre-E: φ: E → G, the class-group map
- **Math**: φ(ε) = [∏_{εs=1} 𝔓_s · ∏_{εs=0} c𝔓_s] ∈ ClassGroup(𝒪_K).
- **Lean**: Requires the split prime pairs from Pre-B. Product of fractional ideals maps to ClassGroup via `ClassGroup.mk0`. But the 𝔓_s themselves are not constructible without Chebotarev.
- **Status**: ❌ Not available (depends on Pre-B)

### Pre-F: h_card_ratio: exp((t·log2 - log_H)·f) + 1 ≤ |E|/|G|
- **Math**: |E| = 2^{tf}, |G| = h(K_j) ≤ H_ℓ^f. So |E|/|G| ≥ 2^{tf}/H_ℓ^f = exp((t·log2 - log H_ℓ)·f).
- **Lean**: Needs class number bound h(K) ≤ H_ℓ^f (not in Mathlib directly).
- **Status**: ❌ Not available

### Pre-G: mk_unit ε₁ ε₂: choose αε₁ ∈ K× with (αε₁) = φ(ε₁)·φ(ε₂)⁻¹
- **Math**: Since φ(ε₁) = φ(ε₂), the ideal 𝔄ε₁·𝔄ε₂⁻¹ is principal. Choose a generator.
- **Lean**: `ClassGroup.mk0_eq_mk0_iff` + `Submodule.IsPrincipal` + choice axiom.
- **Status**: ⚠️ Partially (ClassGroup API exists; need axiom of choice for the generator)

### Pre-H: mk_unit_mem_Λ: αε₁/c(αε₁) ∈ Λ
- **Math**: Q²·(αε₁/c(αε₁)) ∈ 𝒪_K (valuation argument: poles above q_b's with order ≤ 2, Q² kills them).
- **Lean**: Requires valuation theory for K at the primes 𝔓_s, c𝔓_s. `Ideal.spanSingleton_eq_top`, `Valuation`, etc.
- **Status**: ❌ Not directly available (needs split prime API + valuation argument)

### Pre-I: mk_unit_norm: ‖σ_r(αε₁/c(αε₁))‖ = 1
- **Math**: Direct from cm_norm_div_conj_eq_one (already proved in §4).
- **Lean**: `cm_norm_div_conj_eq_one` in NumberFieldDeep.lean §4. But need to convert from `normAtPlace` to `‖mk_unit r‖`.
- **Status**: ⚠️ Core lemma proved; bridge to Fin f → ℂ type needs type bridge

### Pre-J: mk_unit_inj: ε₂ ≠ ε₃ in same fiber → mk_unit ε₁ ε₂ ≠ mk_unit ε₁ ε₃
- **Math**: αε₂/c(αε₂) = αε₃/c(αε₃) → αε₂/αε₃ ∈ K⁺ [by complexConj_eq_self_iff] → valuation contradiction.
- **Lean**: `IsCMField.complexConj_eq_self_iff` available; valuation argument needs split prime API.
- **Status**: ❌ Not available (depends on split prime API + valuation argument)

---

## Summary Table

| Prerequisite | For Sorry 1 | For Sorry 2 | Lean Status |
|-------------|-------------|-------------|-------------|
| Dirichlet APs / primes r ≡ 1 mod 3 | Pre-1 | — | ❌ Not in Mathlib |
| Cyclic cubic subfields of cyclotomic | Pre-2 | — | ❌ Not available |
| Conductor-discriminant formula | Pre-3,4 | — | ❌ Not available |
| d(G), r(G) for pro-p groups | Pre-5,6 | — | ❌ Not in Mathlib |
| Golod-Shafarevich inequality | Pre-7 | — | ❌ Not in Mathlib |
| Chebotarev density theorem | Pre-8 | — | ❌ Not in Mathlib |
| Infinite pro-p tower | Pre-9,10 | — | ❌ Not available |
| CM field K = F(i), IsCMField | Pre-11 | Pre-A | ⚠️ Partial (IsCMField exists) |
| Split prime pairs (𝔓, c𝔓) | Pre-15 | Pre-B,E | ❌ Not available |
| Type bridge mixedSpace → Fin f → ℂ | Pre-12 | Pre-I,J | ⚠️ Buildable (tools exist) |
| IsAddFundamentalDomain (transport) | Pre-13 | — | ⚠️ Mostly available |
| volume F < ∞ | Pre-14 | — | ✅ Available |
| Fintype ClassGroup | — | Pre-D | ✅ Available |
| Sign vector type E | — | Pre-C | ✅ Available |
| Class number bound h(K) ≤ H^f | — | Pre-F | ❌ Not available |
| mk_unit construction via αε/c(αε) | — | Pre-G,H | ❌ Needs split prime API |
| norm = 1 (§4 lemmas) | — | Pre-I | ✅ Proved (in §4) |
| Injectivity (valuation argument) | Pre-15 | Pre-J | ❌ Needs split prime API |

Legend: ✅ Done, ⚠️ Partially available, ❌ Not available

---

## Conclusion

Both sorries depend critically on:
1. **Golod-Shafarevich pro-p group theory** — not in Mathlib
2. **Chebotarev density theorem** — not in Mathlib  
3. **Split-prime API for CM fields** — not in Mathlib
4. **Class number bound via root discriminant** — not directly in Mathlib

The sorry stubs correctly document these gaps. The formalization cannot be completed without either:
- New Mathlib developments in these areas, OR
- Further weakening of the sorry specifications (accepting more abstract inputs), OR
- Asserting the existence as axioms (which the project already does via `sorry`)
