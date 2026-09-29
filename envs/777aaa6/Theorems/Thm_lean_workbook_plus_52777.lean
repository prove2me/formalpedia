-- Prove2me | Theorems.Thm_lean_workbook_plus_52777
-- name    : lean_workbook_plus_52777
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/93af4f6c-7f59-4314-9ac5-e6799352a1a1
-- statement:
--   Prove that $f(x)+f(y)=2f \left( \frac{x+y}{2} \right)$ for all $x,y>0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52777 (f : ℝ → ℝ) (hf: ∀ x y : ℝ, x > 0 ∧ y > 0 → f x + f y = 2 * f (x + y) / 2) : ∀ x y : ℝ, x > 0 ∧ y > 0 → f x + f y = 2 * f (x + y) / 2   :=  by sorry
