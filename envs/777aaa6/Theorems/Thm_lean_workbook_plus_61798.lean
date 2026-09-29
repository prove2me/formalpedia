-- Prove2me | Theorems.Thm_lean_workbook_plus_61798
-- name    : lean_workbook_plus_61798
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/ae22c549-66ca-4d68-b869-3a01e0f30e90
-- statement:
--   $1+2+...+15 = \frac{(15)(14)}{2}$ on this year's AIME
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61798 : ∑ k in Finset.range 15, k = 15 * 14 / 2   :=  by sorry
