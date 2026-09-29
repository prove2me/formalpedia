-- Prove2me | Theorems.Thm_lean_workbook_plus_59550
-- name    : lean_workbook_plus_59550
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/6faaaddd-2923-4f05-a877-d002337324a6
-- statement:
--   And so $\boxed{\text{S2 : }f(x)=x^2+a\text{ }\forall x}$ which indeed is a solution, whatever is $a\in\mathbb R$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59550 (f : ℝ → ℝ) (a : ℝ) (hf: f = fun x ↦ x^2 + a) : (∀ x, f x = x^2 + a)   :=  by sorry
