-- Prove2me | Theorems.Thm_lean_workbook_plus_62182
-- name    : lean_workbook_plus_62182
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/eedc15f2-cf6d-4a1d-97f3-7e2548cd263e
-- statement:
--   let $\frac{x-1}{2} = \frac{4-y}{2} = \frac{z-6}{3} = t$ Then $x = 2t+1$, $y=4-2t$, $z=3t+6$ Solving $x>0, y>0, z>0$ gives $-\frac{1}{2} < t < 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62182  (x y z t : ℝ) (h₀ : x = 2 * t + 1) (h₁ : y = 4 - 2 * t) (h₂ : z = 3 * t + 6) (h₃ : 0 < x ∧ 0 < y ∧ 0 < z) : -(1 / 2) < t ∧ t < 2   :=  by sorry
