-- Prove2me | Theorems.Thm_lean_workbook_plus_70165
-- name    : lean_workbook_plus_70165
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/f5197280-03fb-4b56-89c8-547f90af39ab
-- statement:
--   Given $f(x + y) = f(x) + f(y)$ and $f(1) = 3$, find $f(2)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70165 (f : ℝ → ℝ) (hf : ∀ x y, f (x + y) = f x + f y) (h : f 1 = 3) : f 2 = 6   :=  by sorry
