# Hajir–Maire 2017 — analytic Lie extensions with tame ramification

**Paper:** F. Hajir, C. Maire, *"Analytic Lie extensions of number fields with cyclic fixed points and tame ramification"*, arXiv:1710.09214 (Oct 2017).
**Local PDF:** `assets/hajir_maire_analytic_lie.pdf` (44 pages).

## Why this matters

Companion / precursor to HMR 2021 (`assets/hmr_2021_src/`).  Provides additional
background on:
- p-adic analytic Galois groups
- Uniform pro-p groups (relevant to GS towers)
- The Fontaine–Mazur conjecture (which predicts that tame analytic extensions
  are RAMIFIED at primes above p, with implications for our BRD construction)

## Structure

- **Part I**: Uniform groups and fixed points (Schur–Zassenhaus, uniform pro-p)
- **Part II**: Arithmetic results (T-units, prescribed ramification)
- **Part III**: Proof of main results

## Connection to our sorries

For `gs_cm_tower`:
- §4 on uniform pro-p groups gives the algebraic backbone for pro-p extensions
  with controllable structure.
- §7 on "ramification with prescribed Galois action" is relevant to the tame
  ramification in HMR's BRD construction.

For `chebotarev_fixed_Q`:
- The construction of extensions where specific primes split completely is
  intimately connected to fixed points of σ in the Galois group, discussed
  throughout the paper.

## Bottom line

A supporting reference; the primary citation remains HMR 2021 (`Cutting towers...`).
Hajir–Maire 2017 is useful for the uniform pro-p machinery if a Mathlib
formalization of the GS tower attempts to use the analytic Lie group framework.
