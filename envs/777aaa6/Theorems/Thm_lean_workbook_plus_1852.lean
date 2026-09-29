-- Prove2me | Theorems.Thm_lean_workbook_plus_1852
-- name    : lean_workbook_plus_1852
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/fc4ae9ae-4053-440e-80d9-09c297c3ebc5
-- statement:
--   $\boxed{\text{S2 : }f(x)=x^2+a\quad\forall x}$ which indeed is a solution, whatever is $a\in\mathbb R$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1852 (a : ℝ) (f : ℝ → ℝ) (hf: f = fun x ↦ x^2 + a) : (∀ x, f x = x^2 + a)   :=  by sorry
