-- Prove2me | Theorems.Thm_lean_workbook_plus_44727
-- name    : lean_workbook_plus_44727
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/e47becb4-29ca-416f-bd1f-2f4afdb328eb
-- statement:
--   And so $\boxed{f(x)=a}$ $\forall x$ , which indeed is a solution, whatever is $a\in\mathbb R$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44727 (f : ℝ → ℝ) (hf: f = fun x ↦ a) : f x = a ∧ ∀ x, f x = a   :=  by sorry
