-- Prove2me | Theorems.Thm_lean_workbook_plus_984
-- name    : lean_workbook_plus_984
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/4e792833-04d3-43bc-8475-c41e3791e613
-- statement:
--   Prove that $ \frac {1} {a} = \frac {1} {a+1} + \frac {1} {a(a+1)}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_984 : ∀ a : ℝ, a ≠ 0 ∧ a ≠ -1 → 1/a = 1/(a + 1) + 1/(a*(a + 1))   :=  by sorry
