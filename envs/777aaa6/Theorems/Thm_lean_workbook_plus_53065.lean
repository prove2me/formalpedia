-- Prove2me | Theorems.Thm_lean_workbook_plus_53065
-- name    : lean_workbook_plus_53065
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/19b90d8e-bcf3-423e-a2c7-e1a33db77f3a
-- statement:
--   Following inequality is true:\n$ a,b,c>0,ab+bc+ca=3\Rightarrow abc(a+b+c)\le 3 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53065 (a b c : ℝ) (hab : a > 0 ∧ b > 0 ∧ c > 0) (habc : a * b + b * c + c * a = 3) : a * b * c * (a + b + c) ≤ 3   :=  by sorry
