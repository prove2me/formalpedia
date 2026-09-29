-- Prove2me | Theorems.Thm_lean_workbook_plus_70641
-- name    : lean_workbook_plus_70641
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/3c3e1559-a514-4dd8-9f55-a3d8aec4c600
-- statement:
--   Show that $\sin^{4} x \equiv \frac{1}{8}(\cos 4x -4\cos2x+3)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70641 : ∀ x : ℝ, sin x ^ 4 = 1 / 8 * (cos 4 * x - 4 * cos 2 * x + 3)   :=  by sorry
