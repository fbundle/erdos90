# Gap S3: Lattice Scaling by Q²

## Q9: API for Scaling and Fundamental Domains

**Scaling the Lattice**:
- To scale the lattice by $Q^{-2}$, you can use `LinearEquiv.smul` (if available) or `LinearEquiv.units_smul` on the target space `Fin f → ℂ`.
- `mixedSpace K` is a `Module ℝ`, so you can use `(Q ^ 2 : ℝ)⁻¹ • v`.
- To update the basis:
  ```lean
  let basis_Q := basis.map (LinearEquiv.units_smul ℝ (Fin f → ℂ) (Units.mk0 (Q^2 : ℝ) hQ))
  ```
  (Note: Need to ensure $Q \neq 0$).

**Fundamental Domain Scaling**:
- `ZSpan.map_fundamentalDomain`: `f '' (fundamentalDomain b) = fundamentalDomain (b.map f)`.
- This lemma (in `Mathlib/Algebra/Module/ZLattice/Basic.lean`) confirms that the fundamental domain of the scaled basis is just the scaled image of the original fundamental domain.
- `volume (fundamentalDomain (b.map f)) = |det f| * volume (fundamentalDomain b)`.

## Q10: Separation Bound Threading

**Approach Recommendation**:
The cleanest approach is **(b) change `base.D₀` to $Q^2$ for the tower level**.
- In `GSTowerData`, `D₀` is a property of the whole tower.
- However, each level $K$ has its own denominator $Q_K^2$ arising from the split primes at that level.
- If `base.D₀` is intended to be a *lower bound* on the required scaling, you can scale by $Q_K^2$ as long as $Q_K^2 \ge \text{base}.D_0$.
- In `gs_tower_levels_proved`, you should construct the lattice $\Lambda_K = \Phi(Q_K^{-2} \mathcal{O}_K)$.
- The separation bound will then be $\forall v \in \Lambda_K, v \neq 0 \implies \exists i, \|v i\| \ge Q_K^{-2}$.
- If the return type requires `base.D₀⁻¹`, you must ensure $Q_K^{-2} \ge \text{base}.D_0^{-1}$, which is $Q_K^2 \le \text{base}.D_0$? No, $Q_K^2 \ge \text{base}.D_0$.
- Since $D_0$ in the paper is a constant that just needs to be "large enough," setting $D_0 = Q^2$ at each level is correct.

**Implementation Hint**:
Use `NumberField.mixedEmbedding_injective` and the product formula on $a \in \mathcal{O}_K \setminus \{0\}$.
$\prod \| \Phi(a)_w \|^{mult_w} = |N(a)| \ge 1$.
For totally complex fields, $mult_w = 2$.
$\prod \| \Phi(a)_w \|^2 \ge 1 \implies \exists w, \| \Phi(a)_w \| \ge 1$.
Then for $v = \Phi(Q^{-2} a)$, we have $\| v_w \| = Q^{-2} \| \Phi(a)_w \| \ge Q^{-2}$.
This gives the separation with $D_0 = Q^2$.
