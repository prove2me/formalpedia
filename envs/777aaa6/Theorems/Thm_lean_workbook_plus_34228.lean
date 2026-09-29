-- Prove2me | Theorems.Thm_lean_workbook_plus_34228
-- name    : lean_workbook_plus_34228
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/f67f9fc6-d23b-4ede-8c72-dc2195f28b42
-- statement:
--   Let $a,b>0$ such that $\frac{4}{a+b}+\frac{1}{b}=1 $. Prove that $a(2b-3)\leq 9$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34228 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 4 / (a + b) + 1 / b = 1) : a * (2 * b - 3) ≤ 9   :=  by sorry
