-- Prove2me | Theorems.Thm_lean_workbook_plus_16259
-- name    : lean_workbook_plus_16259
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/e4173608-a310-43f6-b6ac-60c5fbe3198c
-- statement:
--   Examples : \n $f(x)=0$ $\forall x\ne 2$ and $f(2)=3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16259 (f : ℝ → ℝ) (hf: f = fun x => if x ≠ 2 then 0 else 3) : f x = if x ≠ 2 then 0 else 3   :=  by sorry
