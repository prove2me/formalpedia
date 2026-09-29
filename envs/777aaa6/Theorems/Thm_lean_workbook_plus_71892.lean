-- Prove2me | Theorems.Thm_lean_workbook_plus_71892
-- name    : lean_workbook_plus_71892
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/d3abc488-d763-481a-92a5-d9ecbad4434a
-- statement:
--   Prove that $\sin^2(a)=\frac{1-\cos(2a)}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71892 : ∀ a : ℝ, sin a ^ 2 = (1 - cos (2 * a)) / 2   :=  by sorry
