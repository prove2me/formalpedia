-- Prove2me | Theorems.Thm_lean_workbook_plus_70390
-- name    : lean_workbook_plus_70390
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/ca965fea-f4f4-4b00-9b67-c0c42b6e6d48
-- statement:
--   And so $\boxed{\text{S2 : }f(x)=x^2+a\quad\forall x}$ which indeed is a solution, whatever is $a\in\mathbb R$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70390 (a : ℝ) (f : ℝ → ℝ) (hf: f = fun x ↦ x^2 + a) : (∀ x, f x = x^2 + a) ∧ (∀ x, f x = x^2 + a)   :=  by sorry
