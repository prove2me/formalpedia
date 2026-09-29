-- Prove2me | Theorems.Thm_lean_workbook_plus_55734
-- name    : lean_workbook_plus_55734
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/1a6d1023-e2f6-4062-ad1f-cd252441f507
-- statement:
--   Show that $\sin((k+1)y)+\sin((k-1)y)=2\sin(ky)\cos(y)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55734 : ∀ k y : ℝ, sin ((k + 1) * y) + sin ((k - 1) * y) = 2 * sin (k * y) * cos y   :=  by sorry
