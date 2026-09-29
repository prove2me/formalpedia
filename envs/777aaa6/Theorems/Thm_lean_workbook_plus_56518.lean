-- Prove2me | Theorems.Thm_lean_workbook_plus_56518
-- name    : lean_workbook_plus_56518
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/0d14a157-66ad-4183-8245-15a879182a53
-- statement:
--   And so $\boxed{f(x)=ax^2+bx}$ $\forall x$ which indeed is a solution whatever are $a,b\in\mathbb R$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56518 (f : ℝ → ℝ) (a b : ℝ) (hf: f = fun x ↦ a * x ^ 2 + b * x) : ∀ x, f x = a * x ^ 2 + b * x   :=  by sorry
