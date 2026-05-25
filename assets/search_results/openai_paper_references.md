# OpenAI Paper — Full Reference List and Key Propositions from Appendix A

Source: `assets/unit-distance-proof.pdf`, pages 15–18

---

## Full Bibliography (paper's references)

| Tag | Full Citation |
|-----|---------------|
| [Neu99] | Jürgen Neukirch. *Algebraic Number Theory*. Grundlehren der mathematischen Wissenschaften, vol. 322. Springer, Berlin, 1999. Translated by Norbert Schappacher. |
| [Lan94] | Serge Lang. *Algebraic Number Theory*. Graduate Texts in Mathematics, vol. 110. Springer, New York, second edition, 1994. |
| [Was97] | Lawrence C. Washington. *Introduction to Cyclotomic Fields*. Graduate Texts in Mathematics, vol. 83. Springer, New York, second edition, 1997. |
| [NSW08] | Jürgen Neukirch, Alexander Schmidt, and Kay Wingberg. *Cohomology of Number Fields*. Grundlehren, vol. 323. Springer, Berlin, second edition, 2008. |
| [Koc02] | Helmut Koch. *Galois Theory of p-Extensions*. Springer Monographs in Mathematics. Springer, Berlin, 2002. |
| [RZ10] | Luis Ribes and Pavel Zalesskii. *Profinite Groups*. Ergebnisse der Mathematik, vol. 40. Springer, second edition, 2010. |
| [DdSMS99] | John D. Dixon, Marcus P. F. du Sautoy, Avinoam Mann, and Dan Segal. *Analytic Pro-p Groups*. Cambridge Studies in Advanced Mathematics, vol. 61. Cambridge University Press, second edition, 1999. |
| [GS64] | E. S. Golod and I. R. Shafarevich. On the class field tower. *Izv. Akad. Nauk SSSR Ser. Mat.*, 28(2):261–272, 1964. English translation: Amer. Math. Soc. Transl. (2) 48 (1965), 91–102. |
| [GS65] | E. S. Golod and I. R. Shafarevich. On class field towers. *American Mathematical Society Translations, Series 2*, vol. 48, pages 91–102, 1965. |
| [HM01] | Farshid Hajir and Christian Maire. Asymptotically good towers of global fields. *European Congress of Mathematics, Vol. II (Barcelona, 2000)*, Progress in Mathematics vol. 202, pages 207–218. Birkhäuser, 2001. |
| [HMR21] | Farshid Hajir, Christian Maire, and Ravi Ramakrishna. Cutting towers of number fields. *Annales Mathématiques du Québec*, 45(2):321–345, 2021. |
| [Sha63] | Igor R. Shafarevich. Extensions à points de ramification donnés. *Publications Mathématiques de l'IHÉS*, 18:71–92, 1963. (in Russian) |
| [Sha66] | Igor R. Shafarevich. Extensions with given points of ramification. *American Mathematical Society Translations, Series 2*, 59:128–149, 1966. English translation by J. W. S. Cassels. |
| [Tsc26] | N. Tschebotareff. Die Bestimmung der Dichtigkeit einer Menge von Primzahlen… *Mathematische Annalen*, 95(1):191–228, 1926. |
| [Dav00] | Harold Davenport. *Multiplicative Number Theory*. Graduate Texts in Mathematics, vol. 74. Springer, third edition, 2000. |

---

## Key Propositions from Appendix A

### Definition A.4 (CM Fields, page 15)
A CM field is a totally imaginary quadratic extension K/K⁺ of a totally real field. The nontrivial automorphism of K/K⁺ is denoted c. In the paper K = L(i), with L totally real, and **for every complex embedding σ : K ↪ ℂ: σ(c(α)) = σ̄(α)**. Consequently, elements u with u·c(u) = 1 have |σ(u)| = 1 in every complex embedding.

### Proposition A.11 (Cyclotomic splitting, page 16)
If r is a rational prime with r ≡ 1 (mod 3), the unique cyclic cubic subfield of ℚ(ζ_r) is totally real, has conductor r, and is ramified only at r.  
**Reference**: [Was97, Chapter 3, Theorem 3.11] and [Neu99, Chapter VI].

### Proposition A.12 (Chebotarev density theorem, page 16)
After excluding finitely many bad primes, infinitely many rational primes split completely in any prescribed finite Galois extension of ℚ.  
**Reference**: [Neu99, Chapter VII, Section 13] and [Tsc26].

### Proposition A.13 (Minkowski's ideal-class bound, page 16) ← **KEY FOR `h_card_ratio`**
"Minkowski's ideal-class bound, combined with the elementary divisor-function bound for the number of ideals of a given norm, gives h(K) ≤ max{2, rd(K)}^{O([K:ℚ])}, with an absolute implicit constant. Equivalently, when rd(K) ≥ 2, h(K) ≤ |D_K|^{O(1)}."  
**References**: [Neu99, Chapter I, Section 5] and [Lan94, Chapter V].

### Definition A.6 (Discriminants, page 15)
The absolute discriminant of L is D_L. For extension M/F, the relative discriminant 𝔡_{M/F} is an ideal of 𝓞_F, and the tower formula is:
```
|D_M| = |D_F|^{[M:F]} · N_{F/ℚ}(𝔡_{M/F})
```

### Definition A.7 (Frobenius elements, page 16)
For a finite Galois extension N/K unramified at 𝔭, the Frobenius element Frob_{𝔓/𝔭} ∈ Gal(N/K) acts on the residue field by x ↦ x^{|𝓞_K/𝔭|}. The prime 𝔭 splits completely in N exactly when this Frobenius class is the identity.  
**Reference**: [Neu99, Chapter VII, Section 13].

---

## Precise References for Each Sorry

### `h_card_ratio` — Class number bound

**Paper location**: Proposition 3.7 (page 12) and Proposition A.13 (page 16).

**Statement**: h(K) ≤ max{2, rd(K)}^{C_class · [K:ℚ]} for an absolute constant C_class.

**References**:
- [Neu99] Chapter I, Section 5: Minkowski's ideal-class bound (states the bound in terms of discriminant)
- [Lan94] Chapter V: class number bound via Minkowski's theorem

**In Lean context**: Applied with K = K_j (CM field), [K_j:ℚ] = 2f_j, rd(K_j) ≤ 2rd(F) (from (4) in paper), log rd(F) = O(ℓ log ℓ) (from equation (6) in paper). Gives h(K_j) ≤ H_ℓ^{f_j} where log H_ℓ = O(ℓ log ℓ).

### `hmk_unit_mem_Λ` — Integrality of u_ε = α/c(α)

**Paper location**: Proposition 2.2 proof (page 7), equation (4).

**Statement**: v_{𝔓_s}(u_ε) = 2(ε_s − η_s) ∈ {-2,0,2} and v_𝔭(u_ε) = 0 for all other primes 𝔭. Since Q = ∏ q_b and q_b𝓞_K has valuation 1 at each 𝔓_s, Q²·u_ε ∈ 𝓞_K.

**No separate reference** — this is elementary from the definition of valuations in Dedekind domains. The key ingredient is the unique factorization of ideals (IsDedekindDomain), which is already in Mathlib.

### `hmk_unit_inj` — Injectivity of mk_unit

**Paper location**: Proposition 2.2 proof (page 7), last paragraph.

**Statement**: "By (4), distinct ε's give distinct valuation vectors, hence distinct elements u_ε."

**Key fact needed**: If v_{𝔓_s}(u_{ε₂}) = v_{𝔓_s}(u_{ε₃}) for all s, then ε₂ = ε₃. From equation (4): v_{𝔓_s}(u_ε) = 2(ε_s − η_s), so the valuation vector determines ε − η, hence ε.

**No separate external reference** — this is elementary from the valuation formula.

---

## Neukirch Chapter Structure (for locating exact lemmas)

| Chapter | Content | Relevant to |
|---------|---------|------------|
| I, §1-3 | Rings of integers, Dedekind domains | All |
| I, §4 | Valuations, discrete valuations | `hmk_unit_mem_Λ`, `hmk_unit_inj` |
| I, §5 | The different and discriminant; Minkowski's bound | `h_card_ratio` |
| I, §6-7 | Extensions of valuations, prime splitting | `hmk_unit_inj` |
| I, §8 | Galois extensions, Galois acts on primes | valuation conjugation |
| I, §11 | (Does not exist; §8-10 cover splitting/ramification) | |
| III, §3 | (Not §3; class number is Ch. I §5 in Neukirch) | |
| VI | Class field theory | Prop 3.2 base field |
| VII, §13 | Chebotarev density theorem | Proposition 3.6 |

**Note**: The search_prompt.txt mentioned "Ch. I §6-7 (valuations)" and "Ch. III §3 (Minkowski bound)" but based on [Neu99] citations in the paper:
- Minkowski bound is actually **Chapter I, Section 5**
- Valuations are **Chapter I, Section 4**
- Galois action on primes is **Chapter I, Section 8** (not §6-7)
- Chebotarev is **Chapter VII, Section 13**
