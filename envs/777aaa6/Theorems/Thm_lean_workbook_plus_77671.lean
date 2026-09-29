-- Prove2me | Theorems.Thm_lean_workbook_plus_77671
-- name    : lean_workbook_plus_77671
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/fdb554e8-6ee4-4e0e-9fd1-fc870b6502dd
-- statement:
--   $\boxed{f(x)=g(x)=a-x}$ $\forall x$ which indeed is a solution, whatever is $a\in\mathbb R$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77671 (x a : ℝ) (f g : ℝ → ℝ) (hf: f x = a - x) (hg: g x = a - x) : f x = g x   :=  by sorry
