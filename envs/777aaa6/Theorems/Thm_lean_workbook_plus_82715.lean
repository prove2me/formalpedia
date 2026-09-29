-- Prove2me | Theorems.Thm_lean_workbook_plus_82715
-- name    : lean_workbook_plus_82715
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/06da1fc7-7c6e-40e6-ac28-d7a8ac4afc62
-- statement:
--   $ \boxed{f(x)=ax^2+bx}$ $ \forall x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82715 (a b : ℝ) (f : ℝ → ℝ) (h₁ : ∀ x, f x = a * x ^ 2 + b * x) : ∃ a b, ∀ x, f x = a * x ^ 2 + b * x   :=  by sorry
