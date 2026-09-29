-- Prove2me | Theorems.Thm_lean_workbook_plus_26300
-- name    : lean_workbook_plus_26300
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/e4e8e02b-c7ed-46fe-847b-ae05d1574b76
-- statement:
--   $\boxed{f(x)=x^2, \forall x\in\mathbb Z}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26300 (f : ℤ → ℤ) (hf: f = fun x => x^2) : ∀ x, f x = x^2   :=  by sorry
