-- Prove2me | Theorems.Thm_lean_workbook_plus_8193
-- name    : lean_workbook_plus_8193
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/21c67090-9541-4a83-9bc3-aa3bcd174d58
-- statement:
--   Given $a+b+c=0$, prove that $a^3+b^3+c^3=3abc$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8193 (a b c : ℂ) (h : a + b + c = 0) : a ^ 3 + b ^ 3 + c ^ 3 = 3 * a * b * c   :=  by sorry
