-- Prove2me | Theorems.Thm_lean_workbook_plus_24728
-- name    : lean_workbook_plus_24728
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/41949601-14d5-451e-8618-898326d6ea24
-- statement:
--   14 choose two is $\frac{14!}{12!*2!}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24728 : (choose 14 2 : ℚ) = (factorial 14)/(factorial 12 * factorial 2)   :=  by sorry
