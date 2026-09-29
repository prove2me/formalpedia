-- Prove2me | Theorems.Thm_Zeta23_Tail_sum_inv_pow_four_le_telescope
-- name    : Zeta23.Tail.sum_inv_pow_four_le_telescope
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:44:43.033794+00:00
-- url     : https://prove2.me/theorems/bad69b86-1f28-4bfb-a38c-f9e1e922cfab
-- title:
--   Telescoped bound for $\sum_k (D + kh)^{-4}$
-- statement:
--   **Setup.** An elementary real-analysis estimate: $D > 0$ is a starting distance, $h > 0$ a step size, and $d$ a natural number; the sum runs over $k = 0, 1, \dots, d$ (Lean's `range (d+1)`).
--
--   **Statement.**
--   $$\sum_{k=0}^{d} \frac{1}{(D + k h)^{4}} \;\le\; \frac{1}{D^{4}} \;+\; \frac{1}{3h}\left(\frac{1}{D^{3}} - \frac{1}{(D + d h)^{3}}\right).$$
--   The point is the comparison $h\,(D + kh)^{-4} \le \tfrac{1}{3}\bigl((D+(k-1)h)^{-3} - (D+kh)^{-3}\bigr)$ (an integral test in telescoped form): after separating the $k = 0$ head term $D^{-4}$, the remaining terms telescope to the stated difference of inverse cubes.
--
--   **Role.** In `Zeta23.Tail.Grid` this is the analytic core of the grid estimate: `grid_sum_le` applies it with $D = \mathrm{dist}(\gamma, I)$ and $h = 2\pi/L$ and then absorbs the constants via `grid_const_bound`, producing $\sum_{k<d}|\gamma - \tau_k|^{-4} \le L\cdot\mathrm{dist}(\gamma, I)^{-3}$ for Proposition [prop:tail].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail/Grid.lean#L40-L60

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Finset Real

theorem Zeta23.Tail.sum_inv_pow_four_le_telescope {D h : ℝ} (hD : 0 < D) (hh : 0 < h) (d : ℕ) :
    ∑ k ∈ range (d + 1), ((D + k * h) ^ 4)⁻¹
      ≤ (D ^ 4)⁻¹ + ((D ^ 3)⁻¹ - ((D + d * h) ^ 3)⁻¹) / (3 * h) := by sorry
