-- Prove2me | Theorems.Thm_lean_workbook_plus_1881
-- name    : lean_workbook_plus_1881
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/a6609ab1-c651-4cb8-894d-32411af84423
-- statement:
--   Let $a,b>0$ and $a+b=a^2+b^2$ . Prove that, \n\n $$a+b\leq a^2+b^2$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1881 (a b : ℝ) (hab : a > 0 ∧ b > 0) (h : a + b = a^2 + b^2) : a + b ≤ a^2 + b^2   :=  by sorry
