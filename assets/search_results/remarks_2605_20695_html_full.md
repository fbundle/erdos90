# Source: https://arxiv.org/html/2605.20695

# Remarks on the Disproof of the Unit Distance Conjecture

**Authors:** Noga Alon, Thomas F. Bloom, W. T. Gowers, Daniel Litt, Will Sawin, Arul Shankar, Jacob Tsimerman, Victor Wang, Melanie Matchett Wood

**arXiv:** 2605.20695v1 [math.CO] 20 May 2026

**License:** CC BY 4.0

---

## Abstract

"We present a short, digested, human-verified version of the recent OpenAI-generated counterexample to the Erdős unit distance conjecture, and a sequence of reflections on it. The argument relies crucially on ideas that may, at least in retrospect, be attributed to Ellenberg-Venkatesh, Golod-Shafarevich, and Hajir-Maire-Ramakrishna."

---

## 1. Introduction

### Main Theorem (1.1)

"There exists ε > 0 such that the following holds. There exists a sequence of point sets 𝒫ᵢ in ℝ² such that |𝒫ᵢ| → ∞ and the number of unit distances in 𝒫ᵢ is at least |𝒫ᵢ|^(1+ε) for all i."

### 1.1 History of the Problem

The unit distance problem originates from Erdős in 1946. Historical context: "A set of n points may have at most O(n^(3/2)) unit distances via noting that the unit distance graph cannot contain a K₂,₃." Current best upper bound: "O(n^(4/3)), is due to Spencer, Szemerédi, and Trotter."

Erdős conjectured: "An upper bound of n^(1+o(1)) was conjectured by Erdős."

### 1.2 Sketch of the Proof

Key steps outlined:

1. "Construct a large set U of magnitude-1 algebraic numbers of bounded denominator D in a number field K, in terms of the class number h(K) and the splitting behavior of various prime ideals."

2. "A key reason for this is that an element of a CM field has absolute value 1 in some embedding if and only if it has absolute value 1 in all embeddings."

3. "The set of unit distance pairs created in W decreases as the root discriminant of K increases, and thus it is advantageous to let K be a finite layer of an infinite class field tower M of Golod-Shafarevich type."

4. "This fixed prime q will split into many primes in K as [K:ℚ] → ∞, and when used appropriately this drowns out the main enemies, the class number h(K) and discriminant Disc K."

### 1.3 Context for the Proof

"The original grid construction can be thought of as an application of Lemma 2.1 to the CM field K = ℚ(i)."

"A novel ingredient of the AI argument is to take [K:ℚ] → ∞."

Connections to analytic number theory: "In classical Diophantine terms... one corollary of the argument is that there exist rational integers D ≥ 1 such that r₂,F(4D²) grows exponentially in [F:ℚ] along an infinite tower of fields F."

---

## 2. Proof and Further Overview

### 2.1 Statements of Main Lemmas

**Lemma 2.1 (Geometry of Numbers):**

Given a full rank lattice Λ in ℂ^f satisfying certain conditions, for any R ≥ 2, "there exists a translate a + Λ of Λ such that the set (a + Λ) ∩ B_R projected onto a coordinate gives a point set 𝒫 in the plane with 2ν(𝒫) ≥ (uπR²/4vδ²)^f and |𝒫| ≤ (9R²/δ²)^f."

Critical observation: "If we can make u > 36v/π and keep u, v, δ constant while letting f → ∞ and still finding lattices satisfying Lemma 2.1, then we have |𝒫| → ∞."

**Lemma 2.2 (Counting Magnitude-1 Elements):**

"Let K be a number field embedded in ℂ. Assume K = K̄, where K̄ denotes the complex conjugate of K. Let P₁,...,Pₛ be pairwise distinct prime ideals of 𝒪_K such that Pᵢ ≠ P̄ⱼ for all 1 ≤ i,j ≤ s."

Result: "|U| ≥ ∏ⱼ₌₁ˢ(kⱼ + 1)/h(K)."

Remark: "Lemma 2.2 is useful only if K is CM" due to Dirichlet's unit theorem.

### 2.2 Proofs of Main Lemmas

**Proof Strategy for Lemma 2.1:**

"By averaging over a ∈ ℂ^f/Λ, there exists a choice of a such that |(a+Λ) ∩ B_{R-1}| ≥ (π(R-1)²/covol(Λ)^(1/f))^f."

"The translation-by-U_Λ argument described before Lemma 2.1 implies that 2ν(𝒫) ≥ |U_Λ| |(a+Λ) ∩ B_{R-1}|."

**Proof of Theorem 1.1:**

Example construction uses: "T = {3,5,7,11,13,17} and S = {101,∞}. We have that L_T = ℚ(√5, √13, √17, √21, √33) and that 101 splits completely in L_T so d(G_T^S) = 5, and r(G_T^S) ≤ 6."

"We take K_j = L_j(i). Let r = ∏_{q ∈ T ∪ {2}} q, which is an upper bound for the root discriminant of any K_j."

Resulting exponent: "The exponent in equation (2.1) can be taken to be approximately 1 + 6.24·10⁻³⁸."

---

## Reflections by Individual Authors

### 3. Noga Alon

"The Erdős unit distance problem [raised in 1946] is among the best known open problems in Combinatorics. It is also arguably the best known problem in Discrete Geometry."

Assessment: "The solution of the problem by the internal model of Open AI is, in my opinion, an outstanding achievement, settling a long-standing open problem."

Broader significance: "The new spectacular solution of the Erdős unit distance problem convinces me that it is hard to overestimate the full potential impact of this change."

### 4. Thomas Bloom

Historical context: "He first asked it in 1946 and returned to it many times. The site erdosproblems.com currently lists 14 separate references."

Erdős prize: "He first offered a monetary reward in 1982, of $300, for a proof or disproof of the upper bound n^(1+o(1)). The first time the higher prize of $500 was offered in print appears to be 1995."

On why counterexample was less surprising: "It was exactly that – a major new idea – that would have been disturbing. A counterexample, on the other hand, was something one could imagine a computer coming up with by trying lots of things and at some point getting lucky."

Why this was missed: The construction "requires the confluence of several different unlikely events" including spending significant time on the problem, "seriously trying to disprove it, despite the oft-repeated belief of Erdős that it is true," and familiarity with "class field theory to recognise that the appropriately phrased question about infinite towers of number fields with appropriate parameters can be solved using existing theory."

### 5. W T Gowers

On initial misunderstanding: "I misunderstood what he was saying and thought that the model had proved an upper bound of n^(1+o(1)). The Zoom call took place in the late afternoon and I spent the evening adjusting my world view."

Philosophical framework proposed: A notion of "Kolmogorov complexity modulo experts" where "the difficulty of a proof [is] the length of the shortest sequence of bits that would provide experts with enough hints to reconstruct the proof."

Key insights on the proof's hint structure:

1. "Look for a counterexample" (potentially 1 bit with high surprisal value)
2. "Take the best known construction and generalize it"
3. "Try a sequence of number fields of increasing degree, but work with prime ideals of bounded norm"

Speculation: "The hint sequence that would have been necessary to guide an expert to Guth and Katz's proof of the Erdős distinct-distances conjecture would have been quite a bit longer."

### 6. Daniel Litt

Background: "After an internal model at OpenAI produced a solution, I was asked to check its correctness by Mark Sellke and Mehtaab Sawhney at OpenAI."

Verification: "It did not take long for me to convince myself that the solution was correct, not to mention quite clever and natural."

On rare solutions: "There are a few examples of relatively well-known open problems resolved via a fairly short, clever argument: famously, the finite field Kakeya conjecture, proven by Dvir; the sensitivity conjecture, proven by Huang."

Structural concern: "The solution requires ideas from areas with which most of those working on the problem are unfamiliar. These explanations, if correct, should cause us some discomfort. They suggest that incentives towards specialization and silo-ing, though understandable, have cost us some high-quality science."

### 7. Will Sawin

Key observation about why mathematicians missed this: "In trying to generalize this, the most natural approach is to take points of absolute value bounded by a large parameter in the ring of integers 𝒪_K of some fixed CM field K. On the other hand, OpenAI's internal model's approach was to take a set of points of absolute value bounded by a fixed parameter in the ring of integers 𝒪_K of a CM field K of increasing degree."

Technical barrier: "Getting from the first approach to the second approach would be much more intuitive if the bounds obtained from the first approach grew with the degree of the field K. However, they do not."

On generalizations: Discusses obstacles to applying similar methods to:
- The distinct distances problem
- The unit distances problem in ℝ³

### 8. Arul Shankar

Assessment: "This is a really impressive piece of work, and I would accept it for any journal without hesitation."

On the proof's originality: "I would consider this to be a very 'human' proof, though a extremely ingenious one."

On the model's approach: "It is noteworthy that a significant majority of the thoughts are trying to construct a counterexample to the widely believed upper bound, rather than trying to prove it."

Conclusion: "This paper demonstrates that current AI models go beyond just helpers to human mathematicians – they are capable of having original ingenious ideas, and then carrying them out to fruition."

### 9. Jacob Tsimerman

Personal experience: "I actually briefly worked on this problem and tried to make a counterexample, but failed to make progress."

On the construction's difficulty: "On Boris Alexeev's suggestion, I thought about this problem with the idea of making a counterexample stemming from a varying family of bounded degree number fields. Increasing degree occurred to me, but is a very scary dynamic and often doesn't work out."

On why it's hard to see: "While it's true in the final solution that nothing is all that surprising, there are many ways to attempt to set this construction up (how big are the primes? How big is the ball? Do you take large products? how much splitting does one insist on - this is a tradeoff with how easy it is to make the field)."

On AI advantage: "This may indicate one way that AI systems have an edge: it's not just that they can try all known methods, but they can play for longer and in more treacherous waters than mathematicians without getting overwhelmed."

### 10. Victor Wang

On connections: "I have not thought much about the problems since, but recently I enjoyed hearing about [Alon, Bucić, Sauermann] from Noga Alon. Only now have I begun to really appreciate the role number theory has to play for special metrics."

On formalization: "The fact that a complete argument can be given in a few pages (assuming background in algebraic number theory at the level of a first or second semester graduate course), as in the present remarks, made the verification process relatively smooth."

Societal question: "When Hajir, Maire, and Ramakrishna wrote their beautiful papers, did they have in mind that an AI might eventually use their work to derive headline results, potentially with significant ensuing financial implications?"

### 11. Melanie Matchett Wood

Counterfactual assessment: "I believe if the level and type of human expertise that is represented on this note had been assembled to find a counterexample to this conjecture a month ago, and those people put in similar amounts of time working on it than they did to reading and thinking about Chat GPT's solution, the mathematicians would have found a counterexample."

Critical institutional point: "However, without the claimed proof by Chat GPT, there is no particular reason anyone would have tried to look for a counterexample, assembled a group of experts with the appropriate expertise, or that the experts would have agreed to turn their attention to this problem."

Warning about future AI use: "This result does not show us all the times AI has claimed to have a proof of something and been wrong. Without that context (which many of us have just from personal experience), it is also easy to draw incorrect conclusions about the current state of AI and research mathematics."

Citation concerns: "There is a history of closely related ideas in the literature, some of which are mentioned above, but which are not appropriately referenced in Chat GPT's paper."

Future guidelines needed: "Mathematicians need to think about what best practices and proper citation is in these kind of situations, and come to a common understanding as a community."

---

## References

Complete bibliography spans 37 entries including foundational works:
- Erdős (1946, 1982, 1990, 1995)
- Spencer, Szemerédi, Trotter (1984)
- Golod-Shafarevich (1964, 1965)
- Ellenberg-Venkatesh (2007)
- Guth-Katz (2015)
- Hajir-Maire-Ramakrishna (2001, 2021)

**Acknowledgements:** Supported by NSF grants, Royal Society, Collège de France, NSERC, Sloan Fellowship, Packard Fellowship, MacArthur Fellowship, and others.
