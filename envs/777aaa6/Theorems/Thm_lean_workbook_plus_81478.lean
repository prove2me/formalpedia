-- Prove2me | Theorems.Thm_lean_workbook_plus_81478
-- name    : lean_workbook_plus_81478
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/f0453118-42ca-4e5f-a56f-bf5cd0e31ccd
-- statement:
--   Find the value of $\\sum_{n = 1}^{20} 2n - 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81478 : ∑ n in Finset.range 20, (2 * n - 1) = 210   :=  by sorry
