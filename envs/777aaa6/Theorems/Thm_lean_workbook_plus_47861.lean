-- Prove2me | Theorems.Thm_lean_workbook_plus_47861
-- name    : lean_workbook_plus_47861
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/5d18195c-6a09-49a6-b7e9-b9e19f37df24
-- statement:
--   Note that the sum of the coefficients is $P(1)$ . Letting $x=0$ gives $2P(1)=2014$ , so $P(1)=1007$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47861 (P : ℝ → ℝ) (h : P = λ x => 1007 * x ^ 2 - 2014 * x + 2014) : P 1 = 1007   :=  by sorry
