-- Prove2me | Theorems.Thm_lean_workbook_plus_5741
-- name    : lean_workbook_plus_5741
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/6e086c9a-b9e7-4d08-b615-71a32bf9c167
-- statement:
--   For all reals $ a,b,c$ we have: $ 3(ab+ac+bc) \leq (a+b+c)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5741 (a b c : ℝ) : 3 * (a * b + a * c + b * c) ≤ (a + b + c) ^ 2   :=  by sorry
