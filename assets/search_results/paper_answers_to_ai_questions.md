# Direct answers from the paper LaTeX source to the AI's questions

Source files: `sawin_2605_20579.tex` (Sawin, 330 lines) and `remarks_2605_20695.tex` (Remarks, 890 lines).
All line numbers refer to those files.

---

## Q1: Which complex embedding is chosen for fin0 (the "first coordinate")?

**Short answer: there is no canonical choice — the paper says "an arbitrarily chosen infinite place v."**

### Sawin paper, Lemma 4 (`lattice-from-ideal`), lines 113–114:

```
Let π : I → R^2 be the composition I → K → K_v ≅ C ≅ R^2, divided by √|α|_v,
for an **arbitrarily chosen infinite place v**.
```

### Remarks paper, proof of Lemma L:unit_expansion, line 592–593:

```
Fix an injective coordinate projection P of the bounded window W := (a+Λ) ∩ B_R.
```

No specific coordinate is singled out. All embeddings K → C are injective (K is a field), so
any coordinate gives an injective projection.

### The separation δ (for the size bound) comes from (Remarks paper, line 540):

```
"Note that since any non-zero element of O_{K_j} has norm at least 1 and thus has
magnitude at least 1 in some complex embedding, we can take δ = p^{-2k}."
```

This gives: **∃ i, |v_i| ≥ p^{-2k}** (existential over i), NOT ∀i or at a specific i.

### Consequence for the Lean hΛ_sep:

The paper's Lemma L:unit_expansion (Remarks line 426–437) states hΛ_sep as:
> "for all non-zero x ∈ Λ, **at least one** coordinate x_i of x has |x_i| ≥ δ"

This is `∃ i, ‖v i‖ ≥ δ`, an existential statement. The Lean `hΛ_sep : ∀ v ≠ 0, ‖v (fin0 hf)‖ ≥ D⁻¹`
is **strictly stronger** than what the paper proves — it requires fin0 specifically, not "some i."

**The reindexing strategy does NOT work.** The argmax coordinate changes with v:
- For α = a + bi ∈ O_{L(i)}, the coordinate j achieving max |φ_j(α)| depends on α.
- There is no single fixed j = fin0 such that |φ_j(α)| ≥ 1 for ALL nonzero α ∈ O_K.
- Counter-example: L = Q(√5), K = Q(√5)(i). The unit ε = ((1−√5)/2) + 0·i ∈ O_K has
  |φ_1(ε)| = (√5−1)/2 ≈ 0.618 < 1 at one embedding.

**Recommended fix**: Change `hΛ_sep` in `AdmissibleFamily` from:
```lean
hΛ_sep : ∀ v ∈ Λ, v ≠ 0 → ‖v (fin0 hf)‖ ≥ D⁻¹
```
to an existential form:
```lean
hΛ_sep : ∀ v ∈ Λ, v ≠ 0 → ∃ i : Fin f, ‖v i‖ ≥ D⁻¹
```
This matches Lemma L:unit_expansion in the paper and is what `cmSeparation_exists` and
`integer_separation` already prove.

Alternatively, use the sup-norm formulation:
```lean
hΛ_sep : ∀ v ∈ Λ, v ≠ 0 → Finset.sup' Finset.univ ⟨fin0 hf, Finset.mem_univ _⟩ (‖v ·‖) ≥ D⁻¹
```

The projection coordinate (fin0) is separate from the separation coordinate: fin0 is used for
injectivity (any fixed embedding gives an injective π since K is a field), and the separation
just needs some coordinate ≥ δ.

---

## Q2: Specific paper sections for the CM field construction

### The CM field K (Remarks paper, lines 510–511):

```
Given such an L, we will use K = L(i) as our CM field, and have
|Disc K| ≤ ∏_{p ∈ T ∪ {2}} p^{2[L:Q]}.  Let f = deg(L).
```

So **K = L(i) where L is the totally real GS tower field**. Complex conjugation is c(a+bi) = a−bi.

### The map mk_unit (Remarks paper, lines 624–627):

```
Taking ratios of the ideals landing in the most frequent ideal class, gives
≥ ∏(k_j+1)/h(K) pairwise distinct principal ideals (α) for which α·ᾱ ∈ O_K×.
Now let u = α/ᾱ ∈ Q^{-2}.
```

So **mk_unit(α) = α/c(α) = α/ᾱ** where ᾱ = complex conjugate = c(α) for K = L(i).

For K = L(i) and α = a + bi (a,b ∈ O_L):
  c(α) = a − bi,  so  mk_unit(α) = (a+bi)/(a−bi) = (a+bi)²/(a²+b²)

### The norm-1 property (hmk_unit_norm) — Remarks paper line 626:

The paper says α·ᾱ ∈ O_K×, so N_{K/L}(α) = α·c(α) is a unit. Then for any embedding φ:
  |φ(α/c(α))| = |φ(α)|/|φ(c(α))| = |φ(α)|/|conj(φ(α))| = |φ(α)|/|φ(α)| = 1.

This is exactly `cm_norm_div_conj_eq_one` — already proved in the Lean code. ✓

To thread through `exists_cm_class_group_data`, instantiate K as a specific CM field (e.g., the
GS tower field K_j = L_j(i)) and apply the existing lemma.

### Injectivity of mk_unit (hmk_unit_inj) — Remarks paper lines 627–628:

```
Observe that the ideals (u) = (α²) are pairwise distinct.
```

**Proof that (u) = (α²)**:
Since α·c(α) ∈ O_K×, the ideal (α·c(α)) = O_K (unit ideal). Thus c((α)) = (α)^{−1}, and:
  (u) = (α/c(α)) = (α)·c((α))^{−1} = (α)·(α) = (α)²

**Proof of pairwise distinctness**:
1. The construction (proof of Lemma pigeons, lines 618–621) gives pairwise distinct
   principal ideals (α) — different ideals J in the fiber give different quotient ideals
   (α) = J·J₀^{−1} (since J ≠ J').
2. Squaring is injective on the free abelian group of fractional ideals, so (α)² ≠ (α')²
   when (α) ≠ (α').
3. Hence (u) = (α²) and (u') = (α'²) are distinct as fractional ideals.
4. Distinct fractional ideals (u) ≠ (u') imply distinct elements u ≠ u'.

**Lean proof of hmk_unit_inj**: If mk_unit(α) = mk_unit(α'), then (mk_unit(α)) = (mk_unit(α'))
as fractional ideals, so (α²) = (α'²), so (α) = (α') (squaring injective on fractional ideal
group), so α and α' generate the same principal ideal, meaning they are in the same class in the
fiber. Under the construction where fiber elements correspond bijectively to ideals J (via β_J
with (β_J) = J·J_m^{−1}), same class means J = J'. Hence α = α'. QED.

### The relative class group G_K (Sawin paper, Lemma 6 = `modified-class-group`, lines 141–157):

```
G_K = {pairs (J, u) : J fractional ideal of K, u generator of N_{K/F}(J)} / ∼
where (J,u) ∼ ((α)J, α·c(α)·u)
```

Exact sequence (line 148):
  O_K× → O_F× → G_K → Cl(K) → Cl(F)
where all maps are the relative norm. Key bound (line 141):
  #G_K ≤ 2^{d+1} · h^{−}(K)

This is the `CMClassGroupData.G` group in the Lean code. The bound uses the relative class
number h^{−}(K) = h(K)/h(F), not h(K) itself — Sawin's improvement over the Remarks paper.

### The ideal construction (Sawin paper, Lemma 7 = `ideal-from-primes`, lines 161–174):

Given split primes S_F of O_F with exponents k, the construction produces:
- fractional ideal I of K
- element α ∈ N_{K/F}(I)
- at least `∏(k(p)+1) / (2^d · h^{−}(K))` elements β ∈ I with β·c(β) = α

These β's give the mk_unit elements. The construction is:
1. Let L = {ideals J of O_K : N_{K/F}(J) = ∏ p^{k(p)}} — size ∏(k(p)+1)
2. Map L → G_K by J ↦ (J·J₀^{−1}, 1)
3. Pigeonhole: some fiber has ≥ #L/#G_K elements
4. For two ideals J, J' in the fiber: J·J'^{−1} = (β), β·c(β) = 1
5. mk_unit(β) = β/c(β) has |mk_unit(β)|_v = 1 for all v ✓

---

## Q3: Separation at split prime vs. all embeddings

The Sawin paper uses a scaled norm `||x|| = sup_v |x_v|/√|α|_v` (Lemma 4, line 114), where
the sup is over ALL infinite places v. The minimum norm bound (line 127) is:
  sup_v |β_v|/√|α|_v ≥ (#(N_{K/F}(I)/(α)))^{−1/(2d)}

This bounds the **sup** (maximum over all coordinates), not a specific coordinate. The
projection π uses one fixed (arbitrary) coordinate.

For the Remarks paper construction (K = L(i), I = p^{-2k} O_K):
  - α = p^{-4k} (so √|α| = p^{-2k} at every place since K is Galois over Q)
  - N_{K/F}(I)/(α) has index p^{4k·f}... wait, actually:
  - The covolume formula gives covol = 2^{-f} δ^{2f} √|Disc K|
  - δ = p^{-2k} is the min of the sup-norm (= p^{-2k} · 1 since nonzero O_K elements have
    N_{K/Q} ≥ 1, hence sup_i |φ_i(α)| ≥ 1)

**This gives sup_i |v_i| ≥ D^{-1}, not |v_{fin0}| ≥ D^{-1} for a fixed fin0.**

---

## Summary for the Lean developer

| Sorry gap | What the paper provides | What Lean currently requires | Fix |
|-----------|------------------------|------------------------------|-----|
| hΛ_sep | ∃i, ‖v i‖ ≥ D^{-1} (sup-norm bound from N_{K/Q}≥1) | ‖v (fin0)‖ ≥ D^{-1} for fixed fin0 | Change to ∃i |
| cmSeparation | Same (transportated via basis) | Same too-strong requirement | Change to ∃i |
| hmk_unit_norm | |φ(α/c(α))| = 1 — PROVED as cm_norm_div_conj_eq_one | Same | Thread existing proof through exists_cm_class_group_data |
| hmk_unit_inj | Distinct (α) → distinct (u) via (u)=(α²) | mk_unit injective on fiber | Use ideal-class distinctness: squaring injective on fractional ideals |

### Paper references (exact locations)

- **CM field K = L(i)**: Remarks §2 proof of Theorem 1.1, line 510
- **mk_unit = α/ᾱ construction**: Remarks proof of Lemma pigeons, lines 619–626  
- **Injectivity "(u)=(α²) pairwise distinct"**: Remarks line 627
- **G_K exact sequence**: Sawin Lemma 6, lines 146–157
- **Pigeonhole fiber construction**: Sawin Lemma 7, lines 161–174
- **Sup-norm separation**: Sawin Lemma 4 (lattice-from-ideal), lines 110–128
- **"Some coordinate ≥ δ"**: Remarks line 540; Sawin Lemma 4 line 127
- **"Projection onto any coordinate is injective"**: Remarks line 540 ("Projection of p^{-2k}O_{K_j} onto any coordinate in the Minkowski embedding is injective")
- **Explicit GS parameters**: Sawin lines 270–274 (T, S_Q, k values for δ=0.014114)
