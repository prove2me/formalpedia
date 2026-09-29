-- Prove2me | Theorems.Thm_lean_workbook_plus_24198
-- name    : lean_workbook_plus_24198
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/2fae874f-a838-409e-ae8a-ba8e7932ffd0
-- statement:
--   Let $a,b,c,d$ be reals such that $a+b+c+d=0$ . Prove that $a^{3}+b^{3}+c^{3}+d^{3}=3(abc+bcd+cda+dab).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24198 (a b c d : ℝ) (h : a + b + c + d = 0) : a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 = 3 * (a * b * c + b * c * d + c * d * a + d * a * b)   :=  by sorry
