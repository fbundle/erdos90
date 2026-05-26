# Anick–Dicks 2017 — mnemonic for graded GS inequality

**Paper:** D. Anick, W. Dicks, *"A mnemonic for the graded-case Golod–Shafarevich inequality"*, arXiv:1508.03231 (v2, 2017).
**Local PDF:** `assets/anick_dicks_gs.pdf` (7 pages).

## Why this matters

This is a clean, self-contained reference for the Golod–Shafarevich inequality
in the GRADED algebra case.  Useful as a Mathlib-PR-shaped starting point for
formalizing the GS inequality.

## The inequality (graded form)

Let `K` be a field and `B = ⊕_{n ∈ ℤ} B_n = K⟨X | R⟩` a ℤ-graded associative
K-algebra with positively-graded generating set X and relation set R.  Set
`b_n := dim_K(B_n)`.  Then:

```
∀ n ∈ ℤ:  Σ_{x ∈ X} b_{n - deg(x)}  ≤  (Σ_{r ∈ R} b_{n - deg(r)}) + b_n
```

## How it's used in HMR 2021

HMR §2 uses the Golod–Shafarevich inequality to show that the maximal pro-p
extension `K_S(F)/F` (unramified outside a finite set S) is INFINITE when the
GS criterion holds:

```
r < d²/4
```

where `d = dim_𝔽_p H¹(G_S, 𝔽_p)` (generator count) and
`r = dim_𝔽_p H²(G_S, 𝔽_p)` (relation count) for `G_S = Gal(K_S(F)/F)`.

## Mathlib formalization path

A clean Mathlib PR would formalize the graded GS inequality first (Anick–Dicks
explicit form), then build the cohomological GS criterion on top.

Components:
1. Graded K-algebras (mostly in Mathlib already).
2. Koszul resolution for free graded algebras.
3. Dimension counting (Hilbert series).
4. The inequality itself.

The Anick–Dicks paper provides a clean proof via the Koszul resolution.

## Connection to our `gs_cm_tower` sorry

`gs_cm_tower` ultimately uses the GS criterion to conclude existence of an
infinite pro-3 extension with bounded root discriminant.  The Anick–Dicks
formulation handles the algebraic content; the geometric content (root
discriminant bound) comes from Martinet-style constructions.
