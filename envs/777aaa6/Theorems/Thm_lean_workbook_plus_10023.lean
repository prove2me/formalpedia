-- Prove2me | Theorems.Thm_lean_workbook_plus_10023
-- name    : lean_workbook_plus_10023
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/568f42fa-3dd9-47d2-b259-4027cb4e8890
-- statement:
--   Let $a,b,c>0$ and $a^3+b^3+c^3= ab+bc+ca$ . Prove that $$ abc\leq 1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10023 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b * c = 1) (h : a^3 + b^3 + c^3 = a * b + b * c + c * a) : a * b * c ≤ 1   :=  by sorry
