-- Prove2me | Theorems.Thm_lean_workbook_plus_80623
-- name    : lean_workbook_plus_80623
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/90a684ea-4051-47d0-a7ee-4f717df897c8
-- statement:
--   And so $\boxed{f(x)=ax+b\quad\forall x}$ which indeed fits, whatever are $a,b\in\mathbb R$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80623 (f : ℝ → ℝ) (a b : ℝ) (h : ∀ x, f x = a * x + b) : ∀ x, f x = a * x + b   :=  by sorry
