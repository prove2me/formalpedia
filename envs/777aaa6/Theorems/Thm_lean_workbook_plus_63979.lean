-- Prove2me | Theorems.Thm_lean_workbook_plus_63979
-- name    : lean_workbook_plus_63979
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/a58ebd87-5225-488f-8f5f-8e450ef16d61
-- statement:
--   Find all function $f:\mathbb{R} \to \mathbb{R}$ such that, \n\n $$f(x+y)=x+f(y), ~~~\forall x,y \in \mathbb{R}.$$\n\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63979 (f : ℝ → ℝ): (∀ x y : ℝ, f (x + y) = x + f y) ↔ ∃ a :ℝ, ∀ x : ℝ, f x = x + a   :=  by sorry
