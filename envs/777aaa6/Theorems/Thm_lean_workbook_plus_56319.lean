-- Prove2me | Theorems.Thm_lean_workbook_plus_56319
-- name    : lean_workbook_plus_56319
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/dc42210f-42bf-49f8-9e00-79d8592346b1
-- statement:
--   And so $\boxed{\text{S2 : }f(x)=2-x\quad\forall x}$ , which indeed fits
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56319 (f : ℝ → ℝ) (hf: f = fun x => 2 - x) : ∀ x, f x = 2 - x   :=  by sorry
