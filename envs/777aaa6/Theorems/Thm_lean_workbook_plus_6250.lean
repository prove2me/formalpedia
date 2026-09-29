-- Prove2me | Theorems.Thm_lean_workbook_plus_6250
-- name    : lean_workbook_plus_6250
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/72f559bb-ff4c-43ee-b1e2-5978b88b21b9
-- statement:
--   Prove that $\left(1 + \frac{1}{1000}\right)^{1000} < 3 < 1001$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6250 : (1 + 1 / 1000) ^ 1000 < 3 ∧ 3 < 1001   :=  by sorry
