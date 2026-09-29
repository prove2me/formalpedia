-- Prove2me | Theorems.Thm_lean_workbook_plus_78078
-- name    : lean_workbook_plus_78078
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/344a01f1-9b64-4486-a229-1127698f5f96
-- statement:
--   For any three sides $a,b,c$ of a triangle, we always have $a^{2}< a(b+c), b^{2}< b(c+a), c^{2}< c(a+b).$ Adding all three again, we obtain $a^{2}+b^{2}+c^{2}< 2(ab+bc+ca)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78078 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^2 + b^2 + c^2 < 2 * (a * b + b * c + c * a)   :=  by sorry
