-- Prove2me | Theorems.Thm_Zeta23_Tail_grid_const_bound
-- name    : Zeta23.Tail.grid_const_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:44:35.852457+00:00
-- url     : https://prove2.me/theorems/1423edd0-7f60-4f67-a3cc-b9d2699567c9
-- title:
--   Elementary bound $D^{-4} + \frac{D^{-3}}{3h} \le L\,D^{-3}$ for the grid constant
-- statement:
--   **Setup.** An elementary inequality between real numbers, used to absorb the telescoped grid sum into a single clean constant. Here $D \ge 1$ plays the role of the distance from a tail zero's ordinate to the window $I = [T, 2T]$, $L \ge 2$ is the logarithmic length, and $h = 2\pi/L$ is the grid step (so $1/(3h) = L/(6\pi)$).
--
--   **Statement.** For all real $D \ge 1$ and $L \ge 2$,
--   $$\frac{1}{D^4} \;+\; \frac{1}{D^3}\cdot\frac{1}{3\,(2\pi/L)} \;\le\; \frac{L}{D^3}.$$
--   As the docstring notes, this is exactly the step "(as $D \ge 1$, $L \ge 2$)" in the paper: the $D^{-4}$ head term is at most $D^{-3} \le (L/2)D^{-3}$, and $L/(6\pi) \le L/2$, giving the stated bound.
--
--   **Role.** In the `Zeta23.Tail.Grid` module it converts the output of the telescoping estimate `sum_inv_pow_four_le_telescope` into the final grid estimate `grid_sum_le`: $\sum_{k<d}|\gamma-\tau_k|^{-4} \le L\cdot\mathrm{dist}(\gamma, I)^{-3}$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail/Grid.lean#L74-L91

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Finset Real

theorem Zeta23.Tail.grid_const_bound {D L : ℝ} (hD : 1 ≤ D) (hL : 2 ≤ L) :
    (D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * (2 * π / L)) ≤ L * (D ^ 3)⁻¹ := by sorry
