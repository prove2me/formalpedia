-- Prove2me | Theorems.Thm_lean_workbook_plus_40075
-- name    : lean_workbook_plus_40075
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/be824db0-65bf-4f2a-9c7f-97815131ff94
-- statement:
--   The sum of numbers 2000 through 2006 is $14021$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40075 ∑ k in (Finset.Icc 2000 2006), k = 14021   :=  by sorry
