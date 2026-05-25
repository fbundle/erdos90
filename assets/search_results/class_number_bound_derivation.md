# Class Number Bound Derivation: h(K_j) ≤ H_ℓ^{f_j}

Source: OpenAI paper `unit-distance-proof.pdf`, pages 12–14 (Step 4)

---

## The Chain of Bounds (paper page 14)

### Step 1: Relative discriminant of K_j/F_j

The CM field K_j = F_j(i). The relative discriminant 𝔡_{K_j/F_j} divides 4𝓞_{F_j}:
```
|D_{K_j}| = |D_{F_j}|^2 · N_{F_j/ℚ}(𝔡_{K_j/F_j}) ≤ |D_{F_j}|^2 · 4^{f_j}
```

### Step 2: Root discriminant of K_j

Taking 2f_j-th roots ([K_j:ℚ] = 2f_j):
```
rd(K_j) = |D_{K_j}|^{1/(2f_j)} ≤ |D_{F_j}|^{1/f_j} · 4^{1/2} = rd(F_j) · 2
```

Since the tower is everywhere unramified, rd(F_j) = rd(F) for all j. So:
```
rd(K_j) ≤ 2 rd(F)
```

### Step 3: Class number bound (Proposition 3.7)

There exists an absolute constant C_class > 0 such that for any number field K:
```
h(K) ≤ max{2, rd(K)}^{C_class · [K:ℚ]}
```

Applied to K = K_j with [K_j:ℚ] = 2f_j and rd(K_j) ≤ 2rd(F):
```
h(K_j) ≤ (2 rd(F))^{C_class · 2f_j}
        = ((2 rd(F))^{2C_class})^{f_j}
        = H_ℓ^{f_j}
```
where H_ℓ := (2 rd(F))^{2C_class} and log H_ℓ = 2C_class · log(2 rd(F)).

### Step 4: log H_ℓ = O(ℓ log ℓ)

From the tower construction (equation (6), page 13):
```
log rd(F) = (1/3) log |D_F| = (2/3) ∑_i log r_i = O(ℓ log ℓ)
```
where r_1,...,r_ℓ are the first ℓ primes ≡ 1 (mod 3) and D = ∏ r_i.

So log H_ℓ = 2C_class · log(2rd(F)) = O(ℓ log ℓ). ✓

---

## What This Means for the Lean Sorry

### Current Lean code structure (line 481-498)

```lean
have h_card_ratio : Real.exp ((t * Real.log 2 - log_H) * (f : ℝ)) + 1 ≤
    (cardE : ℝ) / (cardG : ℝ) := by
  -- cardE = 2^m = 2^{t·f} (exact)
  -- cardG = h(K) ≤ H^f (sorry'd — needs Prop 3.7)
  -- Then: cardE / cardG ≥ 2^{t·f} / H^f = exp((t log 2 - log H)·f)
  sorry
```

### Proof structure (if sorry'd helpers were available)

```lean
-- Helper 1: the class number bound (sorry — needs Minkowski + Neukirch I.5)
have h_classnum : (cardG : ℝ) ≤ Real.exp (log_H * f) := by
  -- cardG = h(K_j) ≤ H_ℓ^{f_j} = exp(log_H · f)
  -- This is Proposition 3.7 of the OpenAI paper
  -- References: [Neu99, Ch. I §5], [Lan94, Ch. V]
  sorry

-- Helper 2: cardE = 2^m (trivial computation)
have h_cardE : (cardE : ℝ) = (2 : ℝ) ^ m := by
  simp [cardE]  -- E = Fin m → Bool, |E| = 2^m

-- Helper 3: 2^m ≥ 2^{t·f} (since m = t'·f ≥ t·f)
have h_m_ge_tf : t * f ≤ m := by ...

-- Combine:
have h_ratio : (2 : ℝ)^(t*f) / Real.exp (log_H * f) ≥ 
    Real.exp ((t * Real.log 2 - log_H) * f) := by
  rw [div_ge_iff (Real.exp_pos _)]
  rw [← Real.exp_add, ← Real.exp_mul]
  ring_nf
  -- (t·log 2 - log_H)·f + log_H·f = t·log 2·f = log(2^{tf})
  ...
```

---

## Proposition 3.7 Proof Sketch (for reference)

**Minkowski's theorem**: Every ideal class in Cl(𝓞_K) contains a representative ideal I with:
```
N(I) = Ideal.absNorm I ≤ (C_Mink · √|D_K|)^{1/n}   where n = [K:ℚ]
```
(Here C_Mink = (4/π)^{r_2} · (n!/n^n) is the Minkowski constant.)

**Counting ideals of bounded norm**: The number of ideals of norm ≤ X in 𝓞_K is at most:
```
∑_{m≤X} d_n(m) ≤ C^n · X · (1 + log X)^{n-1} / (n-1)!
```
where d_n(m) = n-fold divisor function.

**Combined**: h(K) ≤ (number of ideals of norm ≤ Minkowski bound) ≤ C(rd(K))^{O(n)}.

**Mathlib status**: `NumberField.exists_ideal_in_class_of_norm_le` gives existence of ideal with norm ≤ Minkowski bound (available). The counting bound is NOT in Mathlib.

---

## Alternative: Use the `GSTowerData` Bound Directly

The `GSTowerData` structure (from `gs_tower_levels`) already provides the bound as an *assumption*:
```lean
structure GSTowerData (ℓ : ℕ) where
  ...
  h_classnum : h(K_j) ≤ exp(log_H · f_j)  -- supplied by the tower
```

If the `CMClassGroupData` structure is populated from `GSTowerData`, then `hcardG` can directly carry this bound, and `h_card_ratio` becomes a numerical consequence, not a deep ANT fact.

**Check**: Look at whether `CMClassGroupData.hcardG` already encodes `cardG ≤ exp(log_H * f)` as a field.
