-- Prove2me | Theorems.Thm_lean_workbook_plus_54983
-- name    : lean_workbook_plus_54983
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/59fa7b72-bbf5-4345-9e04-21a48f2f696f
-- statement:
--   When $a+b+c=3$ , we have:\n $4a+4b+c=3a+3b+a+b+c=3a+3b+3=3(a+b+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54983 (a b c : ℝ) (h : a + b + c = 3) : 4 * a + 4 * b + c = 3 * (a + b + 1)   :=  by sorry
