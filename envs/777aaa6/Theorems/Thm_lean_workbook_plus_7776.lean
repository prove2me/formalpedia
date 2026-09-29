-- Prove2me | Theorems.Thm_lean_workbook_plus_7776
-- name    : lean_workbook_plus_7776
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/1adae394-9be0-4eeb-8e32-f68e30f2247d
-- statement:
--   Prove that the equation $x^6+x^5+x^4-x^3-x^2+1=0$ does not have any real solution.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7776 : ¬ ∃ x : ℝ, x^6 + x^5 + x^4 - x^3 - x^2 + 1 = 0   :=  by sorry
