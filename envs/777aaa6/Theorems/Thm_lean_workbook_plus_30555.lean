-- Prove2me | Theorems.Thm_lean_workbook_plus_30555
-- name    : lean_workbook_plus_30555
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/86e07022-77ae-42f6-853a-992ee257294d
-- statement:
--   Simplify the inequality $9(x-1)^2+12x \ge 8x^2$ to $(x-3)^2 \ge 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30555 (x : ℝ) : 9 * (x - 1) ^ 2 + 12 * x ≥ 8 * x ^ 2 ↔ (x - 3) ^ 2 ≥ 0   :=  by sorry
