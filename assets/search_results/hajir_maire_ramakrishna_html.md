# Source: https://arxiv.org/html/2011.09822

## Note on URL

The URL https://arxiv.org/html/2011.09822 returns content for an IRS communications paper, not Hajir-Maire-Ramakrishna. The correct paper is arXiv:1901.04354.

The HTML version at https://arxiv.org/html/1901.04354 returns HTTP 404 (no HTML version available for this 2019 paper).

---

## Hajir-Maire-Ramakrishna: "Cutting towers of number fields" (arXiv:1901.04354)

### Full Citation
Farshid Hajir, Christian Maire, and Ravi Ramakrishna,
"Cutting towers of number fields,"
Annales Mathématiques du Québec **45** (2021), 321–345.
arXiv:1901.04354 [math.NT]

### Mathematical Content (from abstract and citations)

#### Main Setup

Let p be a prime, K a number field, and S a finite set of places of K. Let K_S denote the maximal pro-p extension of K unramified outside S. The Golod-Shafarevich criterion gives a sufficient condition for K_S/K to be infinite:

**Golod-Shafarevich Criterion**: If r > d²/4 where d = dim_Fp H¹(G_S(K), Fp) (number of generators) and r = dim_Fp H²(G_S(K), Fp) (number of relations), then G_S(K) = Gal(K_S/K) is infinite.

#### Key Results

**Theorem (Hajir-Maire-Ramakrishna, main result):** Under appropriate hypotheses on the number field K and the set S, one can construct infinite pro-p subextensions of K_S with bounded root discriminant.

**Specifically:** Using Golod-Shafarevich with careful choice of ramification, they obtain:
- New records on Martinet constants μ_r and μ_c for totally real and totally complex cases
- Answer to Ihara's question: infinite asymptotically good extensions where infinitely many primes split completely

#### Martinet Constants

The Martinet constant μ for a signature (r₁, r₂) is defined as:
μ = inf rdiscr(K)
taken over all number fields K with signature (r₁, r₂) having infinite p-class field tower.

The paper achieves new upper bounds on these constants.

#### Bounded Root Discriminant and Asymptotic Goodness

A tower K₀ ⊂ K₁ ⊂ K₂ ⊂ ... is called **asymptotically good** if:
- [Kₙ : Q] → ∞
- rdiscr(Kₙ) := |disc(Kₙ)|^(1/[Kₙ:Q]) is bounded

This is equivalent (by Hermite's theorem) to saying only finitely many fields up to isomorphism appear at each level — but infinite towers can still exist with bounded root discriminant.

#### Split Primes in the Tower

The paper's answer to Ihara's question produces towers where infinitely many rational primes split completely. This is the key feature needed for the unit distance application:

If p splits completely in all Kₙ, then p splits as p·O_{Kₙ} = P₁^(1) · P₂^(1) · ... · P_fₙ^(1) (fₙ = [Kₙ:Q]) with each Pⱼ having residue field F_p. This means many norm-1 elements exist in O_{Kₙ} that are congruent to ±1 mod p.

#### Connection to CM Field Towers

For the unit distance application (arXiv:2605.20579, Sawin), one needs CM field towers (not just arbitrary number field towers). The CM condition K = K̄ (closed under complex conjugation) ensures:
- The ring of integers O_K embeds into ℂ^f via the Minkowski embedding
- The image consists of elements with conjugate pairs of coordinates
- Norm-1 elements project to the unit circle in each ℂ-coordinate

Hajir-Maire-Ramakrishna's work (along with earlier work by Hajir-Maire on asymptotically good towers) provides the tower K₀ ⊂ K₁ ⊂ ... of CM fields with bounded root discriminant and good splitting properties.

#### Earlier Related Work by Hajir-Maire

Reference [19] in arXiv:2605.20695:
> Farshid Hajir and Christian Maire, Asymptotically good towers of global fields, European Congress of Mathematics, Vol. II (2000), Progress in Mathematics vol. 202, Birkhäuser (2001), 207–218.

This 2000 paper established the existence of asymptotically good towers over number fields with bounded root discriminant, building on Golod-Shafarevich. The 2019 "Cutting towers" paper refines and extends these results.

### MSC Classes
- 11R29 (Class numbers, class groups, discriminants)
- 11R37 (Class field theory)
- 11R21 (Other number fields)

### Related Papers by Same Authors
- arXiv:1904.07062: Infinite class field towers of prime power discriminant
- arXiv:1909.03689: Shafarevich group of restricted ramification
- arXiv:2103.09508: Deficiency of p-class tower groups
- arXiv:2204.08408: Ozaki's theorem and p-groups
- arXiv:2208.05007: Tame Zp extensions
- arXiv:2401.05927: Tamely ramified infinite Galois extensions
