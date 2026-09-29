-- Prove2me | Theorems.Thm_lean_workbook_plus_77956
-- name    : lean_workbook_plus_77956
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/389c91c5-f20f-4a8d-9c80-7723e4c8ab7a
-- statement:
--   $f(x)=ax\quad\forall x>0$ , which indeed fits, whatever is $a>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77956 (a : ℝ) (ha : 0 < a) : ∃ f : ℝ → ℝ, ∀ x > 0, f x = a * x   :=  by sorry
