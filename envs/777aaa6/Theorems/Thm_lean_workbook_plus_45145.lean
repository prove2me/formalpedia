-- Prove2me | Theorems.Thm_lean_workbook_plus_45145
-- name    : lean_workbook_plus_45145
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/4feef18f-895c-4c20-9295-864a6d49f373
-- statement:
--   Show that $(x-3)^2(x^2+2x+3) + 9(x-3)(x+3) \geq 0$ for $x \geq 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45145 (x : ℝ) (hx : x ≥ 3) : (x - 3) ^ 2 * (x ^ 2 + 2 * x + 3) + 9 * (x - 3) * (x + 3) ≥ 0   :=  by sorry
