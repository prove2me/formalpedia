-- Prove2me | Theorems.Thm_lean_workbook_plus_44090
-- name    : lean_workbook_plus_44090
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/888e4ca8-f957-44c1-8e7c-6a96b6ed7c71
-- statement:
--   Calculate the value of $1+2+3+...+100$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44090 : ∑ i in Finset.range 101, i = 5050   :=  by sorry
