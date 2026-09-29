-- Prove2me | Theorems.Thm_lean_workbook_plus_53042
-- name    : lean_workbook_plus_53042
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/693a2156-372c-4d81-9d81-ea15bc13a40e
-- statement:
--   The following inequality is true:\nLet a,b,c be sides of a triangle. Prove that:\n $a^{3}+b^{3}+c^{3}-3abc\geq b(c-a)^2+c(a-b)^2+a(b-c)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53042 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^3 + b^3 + c^3 - 3 * a * b * c ≥ b * (c - a)^2 + c * (a - b)^2 + a * (b - c)^2   :=  by sorry
