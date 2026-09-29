-- Prove2me | Theorems.Thm_lean_workbook_plus_52677
-- name    : lean_workbook_plus_52677
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/5205ddb3-a746-4c72-830c-a138799f25fb
-- statement:
--   Let $ x-y=p , x+y-1=q$ we have $ x=\frac{p+q+1}{2} , y=\frac{q-p+1}{2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52677 (x y p q : ℝ) : x - y = p ∧ x + y - 1 = q ↔ x = (p + q + 1) / 2 ∧ y = (q - p + 1) / 2   :=  by sorry
