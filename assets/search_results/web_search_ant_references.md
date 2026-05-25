# Web Search Results: ANT References and Lean Community

Date: 2026-05-25

---

## Task 1: Neukirch — Minkowski Class-Number Bound

**Location in Neukirch:** Chapter I, §5 "Minkowski Theory" and §6 "The Class Number", in *Algebraic Number Theory*, Springer Grundlehren Vol. 322 (1999).

**Minkowski bound (Neukirch Theorem I.6.3 / I.6.5)**:
```
Every ideal class of K contains an integral ideal a of norm
N(a) ≤ M_K := (n!/n^n) · (4/π)^{r₂} · √|disc(K)|
```
where n = [K:ℚ], r₂ = number of pairs of complex embeddings.

**The form h(K) ≤ rd(K)^{C·n} is NOT directly in Neukirch I.5.** It follows from combining:
1. Minkowski bound: h(K) ≤ M_K ~ (n/2πe)^n · rd(K)^{n/2}
2. Counting ideals of bounded norm: number of ideals of norm ≤ B is O(B·d_n(B)) (divisor function bound)
3. Exponential in n: (n/2πe)^n · rd(K)^{n/2} = rd(K)^{C·n} for explicit C

The exact h(K) ≤ max{2, rd(K)}^{C[K:ℚ]} form appears in the Golod–Shafarevich / class-field-tower literature as a consequence. The OpenAI paper cites [Neu99, Ch. I §5] and [Lan94, Ch. V] for Proposition A.13.

**Mathlib status:** `NumberField.exists_ideal_in_class_of_norm_le` gives the Minkowski representative. Counting ideals of bounded norm is NOT in Mathlib.

**Online lecture notes**: MIT 18.785 Lecture 14 (2017) — standard exposition.

---

## Task 2: Adic Valuation Galois Equivariance

**The theorem:** For K/ℚ Galois, σ ∈ Gal(K/ℚ), prime ideal 𝔓 of 𝓞_K:
```
v_{σ(𝔓)}(σ(α)) = v_{𝔓}(α)   for all α ∈ K×
```

**Where it appears:**
- **Neukirch §I.8** (decomposition and inertia): Galois acts transitively on primes above a rational prime; equivariance follows.
- **Marcus "Number Fields" Ch. 4, §4.1**: states σ permutes primes above p with ramification/inertia data preserved. The formula v_{σP}(σα) = v_P(α) follows since v_P(α) = ord_P(α·𝓞_K) and σ(α·𝓞_K) = σ(α)·𝓞_K.
- **Milne ANT (v3.08)** §3: implicit throughout but not a labeled theorem.

**Cleanest proof sketch for Lean:**
Define the P-adic valuation as v_P(α) = n where 𝔓^n ∥ (α). Then:
σ(𝔓^n ∥ (α)) gives σ(𝔓)^n ∥ (σα) since σ is a ring automorphism.

---

## Task 3: Mathlib — Adic Valuation + Galois Equivariance

**Finding: NOT in Mathlib v4.30.0-rc2.**

Searched: `AdicValuation.lean`, `CMField.lean`, `RamificationInertia/*.lean`, `NumberField/Completion/`.

**What Mathlib does have:**
- `RingOfIntegers.mapAlgEquiv (complexConj K) : 𝓞 K ≃ₐ[𝓞 K⁺] 𝓞 K` (CMField.lean line 239)
- `ringOfIntegersComplexConj K : 𝓞 K ≃ₐ[𝓞 K⁺] 𝓞 K`
- `IsDedekindDomain.HeightOneSpectrum.intValuation v`

**What is missing:** No lemma of the form `v.comap σ` or the equivariance formula for ring automorphisms + `HeightOneSpectrum`. No Zulip discussion or PR found.

**Recommended approach for formalization:** Define `conjPrime (𝔓 : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 K)` as image under `ringOfIntegersComplexConj K`, then prove:
```lean
lemma conjPrime_valuation_eq (𝔓 : HeightOneSpectrum (𝓞 K)) (α : K) :
    (conjPrime 𝔓).valuation K (IsCMField.complexConj K α) = 𝔓.valuation K α := by
  -- Proof: both equal the multiplicity of 𝔓 in the ideal (α)
  -- since complexConj maps (conjPrime 𝔓) ↔ 𝔓 and (complexConj α) ↔ (α) after applying conj⁻¹
  sorry -- [Neukirch ANT I.8]
```

---

## Task 4: CM Field Valuation Parity

**The fact:** For β ∈ K⁺ (maximalRealSubfield K) and 𝔓 a split prime:
```
v_{c(𝔓)}(β) = v_{𝔓}(β)
```

**Proof (two lines):** β ∈ K⁺ means c(β) = β. By Galois equivariance: v_{c(𝔓)}(c(β)) = v_{𝔓}(β). But c(β) = β, so v_{c(𝔓)}(β) = v_{𝔓}(β). QED.

**References:** This is treated as immediate from Galois equivariance + fixed-field definition in all sources. No standalone theorem name found.
- Washington "Introduction to Cyclotomic Fields" §1.2 (implicitly)
- Neukirch ANT §I.8 (implicitly)
- Milne CM notes — split primes discussed but not this specific parity statement

**Lean implementation:**
```lean
lemma valuation_eq_of_mem_maxReal (𝔓 : HeightOneSpectrum (𝓞 K))
    (β : K) (hβ : β ∈ maximalRealSubfield K) :
    (conjPrime 𝔓).valuation K β = 𝔓.valuation K β := by
  have hcβ : IsCMField.complexConj K β = β := (IsCMField.complexConj_eq_self_iff K β).mpr hβ
  calc (conjPrime 𝔓).valuation K β
      = (conjPrime 𝔓).valuation K (IsCMField.complexConj K β) := by rw [hcβ]
    _ = 𝔓.valuation K β := conjPrime_valuation_eq 𝔓 β
```

---

## Key Negative Findings

1. **h(K) ≤ rd(K)^{C·n} does NOT appear as a named theorem** in Neukirch I.5. It is a consequence cited in class-field-tower literature.
2. **No Galois-equivariance for HeightOneSpectrum in Mathlib.** Must be proved or sorry'd.
3. **No Zulip discussion** about `HeightOneSpectrum` + automorphisms.
4. **No "valuation parity" theorem** as a standalone result in any reference.

---

## Sources

- Neukirch ANT (Toronto PDF): `https://www.math.utoronto.ca/~ila/Neukirch_Algebraic_number_theory.pdf`
- MIT 18.785 Lecture 14: `https://math.mit.edu/classes/18.785/2017fa/LectureNotes14.pdf`
- Milne ANT v3.08: `https://www.jmilne.org/math/CourseNotes/ANT.pdf`
- Milne CM notes: `https://www.jmilne.org/math/CourseNotes/CM.pdf`
- Marcus "Number Fields": `https://sites.lsa.umich.edu/boblutz/wp-content/uploads/sites/490/2020/02/mrcsnf.pdf`
- Wikipedia Minkowski's bound: `https://en.wikipedia.org/wiki/Minkowski%27s_bound`
- Wikipedia Splitting in Galois extensions: `https://en.wikipedia.org/wiki/Splitting_of_prime_ideals_in_Galois_extensions`
