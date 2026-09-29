-- Prove2me | Theorems.Thm_lean_workbook_plus_19503
-- name    : lean_workbook_plus_19503
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/236ee87f-1ac5-4ecb-b3ae-71ea8ea8aa10
-- statement:
--   Let $a,b,c,d$ be complex numbers with $a+b+c+d=0$ , prove $a^{3}+b^{3}+c^{3}+d^{3}=3(abc+abd+bcd+acd).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19503 (a b c d : ℂ) (h : a + b + c + d = 0) : a^3 + b^3 + c^3 + d^3 = 3 * (a * b * c + a * b * d + b * c * d + a * c * d)   :=  by sorry
