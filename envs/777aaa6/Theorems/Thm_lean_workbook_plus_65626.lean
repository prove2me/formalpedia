-- Prove2me | Theorems.Thm_lean_workbook_plus_65626
-- name    : lean_workbook_plus_65626
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/05dade13-fd34-43b9-814f-09c2f5033dd4
-- statement:
--   Prove that\n $$\frac{1}{a+bc}+\frac{1}{b+ca}+\frac{1}{c+ab} \geq \frac{3}{2}.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65626 : ∀ a b c : ℝ, (1 / (a + b * c) + 1 / (b + c * a) + 1 / (c + a * b) ≥ 3 / 2)   :=  by sorry
