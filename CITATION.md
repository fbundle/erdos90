# Citation

This project formalizes Theorem 1.1 of the OpenAI 2026 paper *"Planar Point
Sets with Many Unit Distances"* (the disproof of the Erdős unit-distance
conjecture).  The Lean 4 development is in `Erdos90/Main.lean`:
`erdos_unit_distance_false`.

On the `master` branch, the theorem depends on **one non-Mathlib axiom**,
`brd_tower_data` (in `Erdos90/NumberFieldDeep_GSTower.lean`), which bundles
the two deep number-theoretic facts the paper invokes.  On the `full` branch,
that axiom is decomposed into four sub-postulates corresponding to specific
multi-month Mathlib contributions.

## Lean dependencies

### Mathlib4

The Lean Mathematical Library, version v4.30.0.  The only Lean dependency.

* Project: https://github.com/leanprover-community/mathlib4
* License: Apache 2.0
* Citation: The mathlib Community, *The Lean mathematical library*, CPP 2020.
* Used as: required via `[[require]]` in `lakefile.toml`.

## Mathematical sources backing the axiom `brd_tower_data`

`brd_tower_data` (the only non-Mathlib axiom on the proof path) bundles two
results.  Each is supported by the following references; when Mathlib gains
the required infrastructure, the axiom becomes a theorem and these citations
move into the corresponding proof.

### (1) HMR 2021 — Golod–Shafarevich CM tower with fixed split primes

For each `ℓ ≥ 2`, the existence of an infinite tower of CM totally-complex
number fields with bounded root discriminant and a tower-fixed product `Q` of
split primes (via Chebotarev / Ihara).

* **Hajir, Maire, Ramakrishna**, *Cutting class field theory towers*,
  arXiv:2103.05382, 2021.  Local copy: `assets/hmr_2021_src/`.  See §3
  `theo:ihara` for the split-prime persistence in the tower.
* **Golod, Shafarevich**, *On the class field tower*, Izv. Akad. Nauk SSSR
  Ser. Mat. 28 (1964), 261–272.  Existence of infinite class-field towers
  via the relation-rank inequality.
* Standard CM lift (tensor the totally-real base field with a controlled
  imaginary quadratic) — e.g. Neukirch, *Algebraic Number Theory*, Ch. III.

Required Mathlib infrastructure:
* General Chebotarev density theorem (currently only Dirichlet density).
* Artin / Hecke L-functions, their meromorphic continuation past `s = 1`
  and non-vanishing on `Re s = 1`.
* Wiener–Ikehara tauberian theorem.
* Golod–Shafarevich inequality + pro-`p` cohomology + p-Hilbert class field.

### (2) Friedman–Louboutin Brauer–Siegel bound for CM fields

For CM totally-complex `K` of complex degree `f ≥ 5` with `rootDiscr K ≤ rd_F`:
`log h_K / f ≤ 2 · log (2 · rd_F)`.

* **Friedman**, *Analytic formulas for the regulator of a number field*,
  Inventiones Math. 98 (1989), 599–622.  Gives `R_K ≥ 1/5` for CM TC `K`.
* **Louboutin**, *Explicit upper bounds for residues of Dedekind zeta
  functions and class numbers of CM-fields*, Math. Comp. 69 (2000), 311–339.
  Gives `Res_{s=1} ζ_K(s) ≤ (4 · rd_F)^f`.  Local copy:
  `assets/louboutin_2000_class_number.pdf`.
* **Brauer**, *On the zeta-functions of algebraic number fields*,
  Amer. J. Math. 69 (1947), 243–250.  Original Brauer–Siegel theorem.
* **Lang**, *Algebraic Number Theory*, 2nd ed., Springer, Ch. XVI.

Required Mathlib infrastructure:
* Functional equation for `NumberField.dedekindZeta` (multi-D Poisson + theta
  function modular transformation + Mellin transform).
* Stark/Tate's class-number formula at `s = 0`.
* Phragmén–Lindelöf interpolation in vertical strips + Stirling-type bounds
  on `Γ` for the boundary estimates.

## Primary paper being formalized

* **OpenAI**, *Planar Point Sets with Many Unit Distances*, 2026.  Local copy:
  `assets/unit-distance-proof.pdf`.  Theorem 1.1 (the main result) is
  formalized as `Erdos90.Main.erdos_unit_distance_false`; Theorem 1.1's
  contrapositive (the explicit refutation of the Erdős unit-distance
  conjecture) is `Erdos90.Main.erdos_bound_false`.

  The paper's Propositions 2.2–3.8 chain decomposes into:
  * **Props 2.3, 2.4** (geometric construction + coset averaging): proved Lean
    in `Erdos90/Geometric.lean` and `Erdos90/CosetAveraging.lean`.
  * **Props 3.2–3.6** (Golod–Shafarevich + Chebotarev + Brauer–Siegel tower):
    bundled into the axiom `brd_tower_data` (see above for backing references).
  * **Prop 3.7** (Minkowski class-number bound): not needed in our chain
    (`C_class := 1` suffices).
  * **Prop 3.8** (admissibility assembly): proved Lean in
    `Erdos90/NumberField.lean`.

## License

Apache 2.0 (matches Mathlib4).  Derivative work attribution per Apache 2.0
applies for any Mathlib lemma directly cited.
