-- Prove2me | Theorems.Thm_lean_workbook_plus_13702
-- name    : lean_workbook_plus_13702
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/86ead26f-dda1-4648-887e-5afb108e5fe0
-- statement:
--   And so $\boxed{f(x)=ax\text{ and }g(x)=-ax\quad\forall x}$ which indeed is a solution, whatever is $a\in\mathbb R$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13702 (f g : ℝ → ℝ) (hf: f = fun x ↦ a * x) (hg: g = fun x ↦ -a * x) : ∀ x, f x + g x = 0   :=  by sorry
