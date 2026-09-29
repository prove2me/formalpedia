-- Prove2me | Theorems.Thm_lean_workbook_plus_75048
-- name    : lean_workbook_plus_75048
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/2d745d29-2ff5-4e67-9393-d8810acbe8d0
-- statement:
--   And so $\boxed{f(x)=2x\\quad\\forall x>0}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75048 (f : ℝ → ℝ) (hf: f = fun (x:ℝ) => 2 * x) (hx: 0 < x) : f x = 2 * x   :=  by sorry
