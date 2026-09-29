-- Prove2me | Theorems.Thm_lean_workbook_plus_3284
-- name    : lean_workbook_plus_3284
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/257d7a25-20e3-4d9d-972f-06dbcf43580f
-- statement:
--   And so $\boxed{\text{S2 : }f(x)=c\text{ }\forall x}$ which indeed is a solution, whatever is $c\in\mathbb R$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3284 (f : ℝ → ℝ) (c : ℝ) (h : ∀ x, f x = c) : ∀ x, f x = c   :=  by sorry
