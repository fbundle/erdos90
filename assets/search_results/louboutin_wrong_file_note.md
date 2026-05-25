# NOTE: assets/louboutin_2000_class_number.pdf is the WRONG PAPER

## What the file actually contains

The file `assets/louboutin_2000_class_number.pdf` is:
- **Title**: "Local Indicators for Plurisubharmonic Functions"
- **Authors**: Pierre Lelong and Alexander Rashkovskii
- **Subject**: Complex analysis / plurisubharmonic functions (completely unrelated to ANT)
- **ArXiv**: math/9901014v1 [math.CV], January 1999

This is NOT the class number paper by Stéphane Louboutin.

## What the correct Louboutin paper is

The paper cited by Sawin as [11, Corollary 3] is:

**Stéphane Louboutin**. "Explicit bounds for residues of Dedekind zeta functions, values of L-functions at s=1, and relative class numbers." *Journal of Number Theory*, **85**(2):263–282, 2000.

**Corollary 3** (the relevant result) states an explicit upper bound for the relative class number h^-(K):
```
h^-(K) ≤ 2 Q_K w_K √(Δ_K/Δ_F) · (e·log(√(Δ_K/Δ_F)) / (4π))^d
```
where:
- Q_K ∈ {1, 2} is the Hasse unit index
- w_K = number of roots of unity in K
- Δ_K, Δ_F = absolute discriminants
- d = [F:ℚ] = half the degree of K

## Impact on the formalization

The `h_card_ratio` sorry requires: h(K) ≤ H^f. This follows from the Louboutin bound on h^-(K) (since h(K) = h^-(K) · h(F) and h(F) is bounded separately). The Sawin paper (Lemma 9) uses this bound.

The Minkowski bound (Proposition A.13 in the OpenAI paper, citing [Neu99, Chapter I, Section 5] and [Lan94, Chapter V]) gives a cruder bound: h(K) ≤ max{2, rd(K)}^{C_class·[K:ℚ]}. This is sufficient for the formalization.

## Recommendation

For the Lean formalization, the Minkowski bound is simpler to state and sufficient. The Louboutin bound is not needed — it's an improvement used by Sawin for the explicit δ calculation but not for the existence proof.
