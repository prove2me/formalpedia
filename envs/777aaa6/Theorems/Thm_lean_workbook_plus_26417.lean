-- Prove2me | Theorems.Thm_lean_workbook_plus_26417
-- name    : lean_workbook_plus_26417
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/1ad3a41f-5ce8-4ffd-b92b-381491ec3792
-- statement:
--   Solution $(y-x)^4\ge0$ and $(x-2)^4\ge0$ , so \n\n $$(y-x)^4+(x-2)^4\ge0$$ and equality occurs if and only if both $y-x=0$ and $x-2=0$ are satisfied, which occurs when $x=y=2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26417  (x y : ℝ) :
  (y - x)^4 + (x - 2)^4 ≥ 0   :=  by sorry
