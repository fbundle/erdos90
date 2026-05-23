# Sorry Gap: `exists_cm_class_group_data` (§5, Prop 2.2)

## Lean Signature

```lean
def exists_cm_class_group_data
    (f : ℕ) (hf1 : f ≥ 1) (D₀ : ℝ) (hD₀ : D₀ > 0)
    (t log_H : ℝ) (ht : t ≥ 0) (hγ_pos : t * Real.log 2 - log_H > 0)
    (Λ : AddSubgroup (Fin f → ℂ))
    (hΛ_sep : ∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf1)‖ ≥ D₀⁻¹) :
    CMClassGroupData f t log_H Λ
```

Must fill all fields of `CMClassGroupData f t log_H Λ`:
- `E : Type`, `G : Type` (finite decidable types)
- `φ : E → G` (class-group map)
- `cardE cardG : ℕ`, `hcardE hcardG`
- `h_card_ratio : exp((t·log 2 - log_H)·f) + 1 ≤ cardE / cardG`
- `mk_unit : E → E → Fin f → ℂ`
- `mk_unit_mem_Λ` — mk_unit ε₁ ε₂ ∈ Λ when ε₁ ≠ ε₂ and φ ε₁ = φ ε₂
- `mk_unit_norm` — ‖mk_unit ε₁ ε₂ r‖ = 1 for all r : Fin f
- `mk_unit_inj` — injectivity on fibers

---

## Mathematical Prerequisites (Prop 2.2 from the paper)

**Required inputs from the GS tower** (already packaged in `GSTowerData`):
- CM field K = F_j(i) of degree [K:ℚ] = 2f (totally imaginary)
- f distinct complex embeddings σ_r: K → ℂ (one extension of each real embedding of F_j)
- D₀ = Q² where Q = ∏ q_b (product of split primes)
- t rational primes q_b ≡ 1 (mod 4), each splitting completely in F_j
- The lattice Λ = Φ(D₀⁻¹ · 𝒪_K) ⊂ Fin f → ℂ via Φ(x) = (σ₁(x),...,σ_f(x))

**The construction (paper §2, Prop 2.2)**:
1. m = tf split prime ideal pairs {𝔓_s, c𝔓_s} in K from the split q_b's
2. E = {0,1}^m (binary sign vectors), |E| = 2^m = 2^{tf}
3. G = ClassGroup(𝒪_K), |G| = h(K) ≤ H_ℓ^f (class-number bound)
4. φ: E → G, φ(ε) = [∏_{εs=1} 𝔓_s · ∏_{εs=0} c𝔓_s]
5. h_card_ratio: |E|/|G| ≥ 2^{tf}/H_ℓ^f = exp((t·log 2 - log H_ℓ)·f) ≥ exp(γ·f) + 1
6. mk_unit ε₁ ε₂: choose αε₁ ∈ K× with (αε₁) = φ(ε₁)·φ(ε₂)⁻¹ [from same ideal class], return Φ(αε₁/c(αε₁))
7. mk_unit_mem_Λ: αε₁/c(αε₁) ∈ Q⁻²𝒪_K = D₀⁻¹·𝒪_K (from valuation argument)
8. mk_unit_norm: ‖σ_r(αε₁/c(αε₁))‖ = 1 (proved: σ_r(c(α)) = conj(σ_r(α)))
9. mk_unit_inj: αε₁/c(αε₁) = αε₂/c(αε₂) → αε₁/αε₂ ∈ K⁺ → same ideal class member → ε₁ = ε₂

---

## What's Available in Mathlib

### Directly usable:
- `IsCMField.complexConj : K ≃ₐ[K⁺] K` — complex conjugation on CM fields
- `IsCMField.complexEmbedding_complexConj (φ : K →+* ℂ) (x : K) : φ(complexConj K x) = conj(φ x)`
- `IsCMField.complexConj_eq_self_iff (x : K) : complexConj K x = x ↔ x ∈ K⁺`
- `IsCMField.ringOfIntegersComplexConj : (𝓞 K) ≃ₐ[𝓞 K⁺] (𝓞 K)`
- Fintype (ClassGroup (𝓞 K)) — finiteness of class group (instFintypeClassGroup)
- `exists_ideal_in_class_of_norm_le (C : ClassGroup (𝓞 K)) : ∃ I, ClassGroup.mk0 I = C ∧ absNorm I ≤ M K`
  where M K = (4/π)^r₂ · (n!/n^n) · √|discr K|  (n = [K:ℚ], r₂ = nrComplexPlaces K)
- `ClassGroup.mk0_surjective` — every class is represented by a nonzero ideal
- `Ideal.absNorm_mul`, `Ideal.absNorm_eq_zero_iff` — norm of product of ideals

### Proved in §4 of NumberFieldDeep (already done):
- `norm_div_star_eq_one` — ‖z/star z‖ = 1 for z : ℂ nonzero
- `cm_norm_div_conj_eq_one` — ‖φ(α/c(α))‖ = 1 at each complex embedding φ
- `normAtPlace_mixedEmbedding_cm_div_conj_eq_one` — normAtPlace = 1 at every infinite place
- `mixedEmbedding_cm_div_conj_complex_norm_one` — ‖(mixedEmbedding K (α/c(α))).2 w‖ = 1

### Proved in §3 of NumberFieldDeep (already done):
- `exists_fiber_ge_div` — pigeonhole on f: α → β, ∃ b with |f⁻¹(b)| ≥ |α|/|β|

---

## What's Missing (in Mathlib v4.29.1)

### 1. The CM field K itself
Need a specific number field K of degree 2f with:
- IsCMField K, IsTotallyComplex K, [K:ℚ] = 2f
- NumberField K instance
The GS tower gives K = F_j(i), but F_j requires Golod-Shafarevich + Chebotarev.

**Workaround**: Use `sorry` or use cyclotomic fields ℚ(ζ_{p^k}) as a placeholder (IsCyclotomicExtension gives IsCMField), but degree control is hard.

### 2. Split prime ideal pairs (𝔓_s, c𝔓_s) in K
No API in Mathlib for "prime ideal q_b of ℤ splits completely in L iff it factors into f·[L:ℚ] distinct primes" in the context of the GS tower.

Available: `Ideal.primesOver`, `inertiaDeg`, `ramificationIdx` — but no theorem "q ≡ 1 mod 4 ∧ q splits in L → q splits in K = L(i)" in the required generality.

**Workaround**: Accept the split prime pairs as part of the sorry structure; their existence follows from Chebotarev (also sorry'd in gs_tower_levels) and the condition q ≡ 1 mod 4.

### 3. Class number bound h(K) ≤ H_ℓ^f
No Lean theorem states h(K) ≤ rd(K)^{C·[K:ℚ]}. The Minkowski bound M K = (4/π)^r₂ · (n!/n^n) · √|discr K| IS formalized. For the tower fields, |discr K| ≤ 4^f · rd(F)^{2f} (from rd(K_j) ≤ 2·rd(F)), so M K can be bounded exponentially in f — but this calculation is not in Mathlib.

The paper's Prop 3.7: h(K) ≤ max{2, rd(K)}^{C_class · [K:ℚ]} with absolute C_class.

**To bound M K ≤ H_ℓ^f** for totally complex K of degree 2f with bounded root discriminant:
```
M K = (4/π)^f · ((2f)!/(2f)^{2f}) · √|discr K|
    ≤ (4/π)^f · 1 · (rd(K)^f)     [since (n!/n^n) ≤ 1 and |discr K|^{1/(2f)} ≤ rd(K)]
    = (4·rd(K)/π)^f
```
This would give h(K) ≤ classNumber ≤ M K ≤ (4·rd(K)/π)^f, but `classNumber K ≤ M K` is not directly stated in Mathlib (it follows from `exists_ideal_in_class_of_norm_le` + pigeonhole over norm-bounded ideals, which requires a separate estimate).

**Concrete bound from Sawin (arXiv:2605.20579, Lemma 9)**:
h^-(K) ≤ 8 · rd_{K/F}^2 · (sqrt(rd_{K/F}) · log(rd_{K/F}) · e/(4π))^f
Since rd_{K/F} ≤ 2 (for K = F(i), relative discriminant divides 4O_F), this gives:
h(K) ≤ h^+(K) · h^-(K) ≤ h(F) · (const)^f where const is explicit.

### 4. Injectivity mk_unit_inj
`mk_unit ε₁ ε₂ = mk_unit ε₁ ε₃ → ε₂ = ε₃` (for fixed ε₁, in the same fiber).

Proof outline (not in Mathlib):
- Φ(αε₂/c(αε₂)) = Φ(αε₃/c(αε₃)) where Φ is injective → αε₂/c(αε₂) = αε₃/c(αε₃)
- αε₂/αε₃ = c(αε₂)/c(αε₃) = c(αε₂/αε₃) → αε₂/αε₃ ∈ K⁺ [by complexConj_eq_self_iff]
- (αε₂)/(αε₃) ∈ K⁺ and (αε₂)/(αε₃) generates ideal (𝔄ε₂ · 𝔄ε₃⁻¹)
- The ideal (𝔄ε₂ · 𝔄ε₃⁻¹) = (αε₂/αε₃) is principal with generator in K⁺
- This forces v_{𝔓_s}(αε₂/αε₃) ∈ 2ℤ but also v_{𝔓_s}(αε₂) - v_{𝔓_s}(αε₃) = 2(ε₂_s - η_s) - 2(ε₃_s - η_s) = 2(ε₂_s - ε₃_s)
- So ε₂_s = ε₃_s for all s, hence ε₂ = ε₃

---

## Suggested Proof Strategy for Lean

Since the full algebraic number theory is not in Mathlib, the sorry is currently necessary. However, the following partial approach can document what would be needed:

### Approach 1: Cyclotomic placeholder (incomplete)
Use K = ℚ(ζ_{p^k}) for suitable p, k. This gives IsCMField K (from `IsCyclotomicExtension.isCMField`), and there IS a CM structure. However, choosing p, k to make [K:ℚ] = 2f for the specific f from the tower is nontrivial.

### Approach 2: Abstract existence (sorry)
The current sorry correctly documents all required fields. The structure `CMClassGroupData` already encodes all necessary properties abstractly. The sorry just needs algebraic number theory not yet in Mathlib.

### Mathlib APIs that would be needed for a full proof:
- API for splitting of primes in CM extensions (need: if q ≡ 1 mod 4 and q splits in F, then each prime of F above q splits into two primes in K = F(i))
- Explicit class number bound: `classNumber K ≤ (4·rd(K)/π)^(finrank ℚ K / 2)` or similar
- `InjOn (fun α => mixedEmbedding K (α / complexConj K α)) (someSet)` — injectivity on the relevant set

---

## References

- OpenAI paper §2, Prop 2.2 (page 6 of unit-distance-proof.pdf)
- Sawin (arXiv:2605.20579), Lemma 7, 9 — explicit construction and class number bounds
- Neukirch, Algebraic Number Theory, Ch. I §6-7 (complexConj), Ch. III §3 (class group)
- Lang, Algebraic Number Theory, Ch. V (class number bounds)
- Mathlib: `CMField.lean` (IsCMField), `ClassNumber.lean` (exists_ideal_in_class_of_norm_le)
