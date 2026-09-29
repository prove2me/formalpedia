-- Prove2me | Theorems.Thm_Zeta23_Tail_sum_window_weights_le
-- name    : Zeta23.Tail.sum_window_weights_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:45:15.130951+00:00
-- url     : https://prove2.me/theorems/6912e4a0-b5c0-4be2-a023-58de4ba3db8e
-- title:
--   Window-weight sum: $\sum_j \max(D_0, j)^{-3}\log(B + j)$ bounded explicitly
-- statement:
--   **Setup.** An elementary summation lemma for the tail count. Let $F$ be a finite set of window indices $j \in \mathbb{N}$, and let $B \ge 1$, $D_0 \ge 2$ be reals with $j + 1 \ge D_0$ for every $j \in F$ (the windows start at distance about $D_0$). Each window $j$ carries the weight $\max(D_0, j)^{-3}$ (the inverse-cube distance weight, floored at $D_0$) times the logarithmic zero count $\log(B + j)$ of that window.
--
--   **Statement.**
--   $$\sum_{j \in F} \frac{\log(B + j)}{\max(D_0, j)^{3}} \;\le\; \left(\frac{2}{D_0^{3}} + \frac{1}{2 D_0^{2}}\right)\log B \;+\; \frac{1}{B}\left(\frac{2}{D_0^{2}} + \frac{1}{D_0}\right).$$
--   The right-hand side is what an integral comparison $\int_{D_0}^\infty x^{-3}\log(B+x)\,dx$ produces, made fully explicit.
--
--   **Role.** In `Zeta23.Tail.Count` this bounds the total weight of the unit windows on one side of the interval $I$; it is consumed by `one_side_sum_le`, and (with $D_0 = \sqrt T$, $B = 2T+4$, doubled for the two sides, via `two_sides_numeric`) feeds the zero-count sum $\sum m_\rho\,\mathrm{dist}(\gamma_\rho, I)^{-3} \le 4A_0\log(4T)/T$ of Proposition [prop:tail].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail/Count.lean#L112-L194

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Real

theorem Zeta23.Tail.sum_window_weights_le (F : Finset ℕ) {B D₀ : ℝ} (hB : 1 ≤ B) (hD₀ : 2 ≤ D₀)
    (hF : ∀ j ∈ F, D₀ ≤ (j : ℝ) + 1) :
    ∑ j ∈ F, ((max D₀ j) ^ 3)⁻¹ * Real.log (B + j)
      ≤ (2 * (D₀ ^ 3)⁻¹ + (D₀ ^ 2)⁻¹ / 2) * Real.log B + (2 * (D₀ ^ 2)⁻¹ + D₀⁻¹) / B := by sorry
