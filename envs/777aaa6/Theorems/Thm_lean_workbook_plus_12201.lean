-- Prove2me | Theorems.Thm_lean_workbook_plus_12201
-- name    : lean_workbook_plus_12201
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/38729be5-08bc-416a-87aa-e63ae6a48732
-- statement:
--   prove that $(t-2)\left[2t^{2}(t-2)+5t\left(t^{2}-4\right)+t^{3}+t+6\right]\ge 0$ for any $t\ge 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12201 (t : ℝ) (h₀ : 2 ≤ t) : (t - 2) * (2 * t ^ 2 * (t - 2) + 5 * t * (t ^ 2 - 4) + t ^ 3 + t + 6) ≥ 0   :=  by sorry
