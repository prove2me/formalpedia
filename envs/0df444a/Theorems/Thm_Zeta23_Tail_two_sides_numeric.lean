-- Prove2me | Theorems.Thm_Zeta23_Tail_two_sides_numeric
-- name    : Zeta23.Tail.two_sides_numeric
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:45:19.783442+00:00
-- url     : https://prove2.me/theorems/632bd3b5-8d0b-4f55-aead-af0ba9019451
-- title:
--   Two-sided numeric bound: window-weight total $\le 4\log(4T)/T$
-- statement:
--   **Setup.** A purely numeric inequality closing the tail count. It evaluates the explicit window-weight bound of `sum_window_weights_le` / `one_side_sum_le` at the concrete choices $D_0 = \sqrt T$ (so $D_0^2 = T$, $D_0^3 = \sqrt T^{\,3}$) and $B = 2T + 4$, doubled to account for the two sides of the window $I = [T, 2T]$. Here $T_0 := 300$.
--
--   **Statement.** For every real $T \ge T_0$,
--   $$2\left[\left(\frac{2}{\sqrt T^{\,3}} + \frac{1}{2\,\sqrt T^{\,2}}\right)\log(2T + 4) \;+\; \frac{1}{2T+4}\left(\frac{2}{\sqrt T^{\,2}} + \frac{1}{\sqrt T}\right)\right] \;\le\; \frac{4\log(4T)}{T}.$$
--
--   **Role.** This is the last, purely computational step of the zero-count sum in `Zeta23.Tail.Count`: it converts the one-sided explicit bounds into the clean form $4A_0\log(4T)/T$ of `tail_count_sum_le`, which in turn drives the bound $\|\tilde E\| \le \theta_0$ of Proposition [prop:tail].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail/Count.lean#L251-L288

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Zeta23_Tail_Basic

open Finset Real
open Zeta23
open Tail

theorem Zeta23.Tail.two_sides_numeric {T : ℝ} (hT : T₀ ≤ T) :
    2 * ((2 * (Real.sqrt T ^ 3)⁻¹ + (Real.sqrt T ^ 2)⁻¹ / 2) * Real.log (2 * T + 4)
          + (2 * (Real.sqrt T ^ 2)⁻¹ + (Real.sqrt T)⁻¹) / (2 * T + 4))
      ≤ 4 * Real.log (4 * T) / T := by sorry
