/-
Copyright (c) 2026 Khanh Nguyen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Khanh Nguyen
-/
import Erdos90.Mathlib4_Extra.ClassFieldTheory

/-!
# Stickelberger's theorem — Mathlib-PR-shape stub

**Stickelberger's theorem** (1890) gives explicit annihilators of the class
group of cyclotomic fields.

## Stickelberger element

For a cyclotomic field `K = ℚ(ζ_n)`, the **Stickelberger element** is
defined as:

  `θ_n = ∑_{a ∈ (ℤ/nℤ)^*} ⟨a/n⟩ · σ_a^{-1} ∈ ℚ[Gal(K/ℚ)]`

where `⟨x⟩` is the fractional part of `x` and `σ_a` is the automorphism
sending `ζ_n` to `ζ_n^a`.

## Stickelberger's theorem

For any `β ∈ ℤ[Gal(K/ℚ)]` such that `β · θ_n ∈ ℤ[Gal(K/ℚ)]`, the element
`β · θ_n` annihilates `ClassGroup (𝓞 K)`.

In particular, when `n` is odd or `n = 2p` with `p` odd prime, the
**Stickelberger ideal** `St(n) = θ_n · ℤ[Gal(K/ℚ)] ∩ ℤ[Gal(K/ℚ)]`
annihilates the class group.

## Why this matters

Stickelberger gives EXPLICIT elements annihilating the class group.  This
is used in:
* Iwasawa theory (cyclotomic Iwasawa main conjecture).
* Class number computations for cyclotomic fields.
* Greenberg's conjecture.

For the HMR construction, Stickelberger relations could in principle be
used to verify the existence of the required pro-`p` Galois group
structure.  But HMR's approach is more elementary (just Golod-Shafarevich).

## What's in Mathlib v4.30

Limited.  Gauss sums (PROVED in `Mathlib/NumberTheory/GaussSum.lean`).
No Stickelberger element / ideal as named objects.

## What this file provides

Labelled stubs for:
* `stickelberger_element` — the Stickelberger element θ_n.
* `stickelberger_annihilator_postulate` — the annihilation theorem.

## References

- Stickelberger 1890.
- Washington *Cyclotomic Fields* Chapter 6.
- Lang *Cyclotomic Fields I+II* Chapter 1.
-/

namespace NumberField

universe u

/-- **Stickelberger element** for `ℚ(ζ_n)` (labelled stub).

The element `θ_n ∈ ℚ[Gal(ℚ(ζ_n)/ℚ)]` is the "average of fractional parts
weighted by Galois inverses".  Stub-only; the precise definition requires
the Galois group ↔ `(ℤ/nℤ)^*` isomorphism. -/
def stickelberger_element_postulate
    (K : Type u) [Field K] [NumberField K] (_n : ℕ)
    [IsCyclotomicExtension {_n} ℚ K] :
    True := sorry

/-- **Stickelberger's annihilation theorem** (postulated):

The Stickelberger ideal annihilates the class group of `ℚ(ζ_n)`. -/
def stickelberger_annihilator_postulate
    (K : Type u) [Field K] [NumberField K] (_n : ℕ)
    [IsCyclotomicExtension {_n} ℚ K] :
    True := sorry

end NumberField
