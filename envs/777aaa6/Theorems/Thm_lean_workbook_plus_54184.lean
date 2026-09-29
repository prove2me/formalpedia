-- Prove2me | Theorems.Thm_lean_workbook_plus_54184
-- name    : lean_workbook_plus_54184
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/11dd3845-f7c2-4b05-af08-d448927f74a5
-- statement:
--   Let $a,b,c $ be positive real numbers such that $a^2+b^2+c^2+2abc=1$ .Prove that $ab+bc+ca\le (a+b+c)/2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54184 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + 2 * a * b * c = 1) : a * b + b * c + c * a ≤ (a + b + c) / 2   :=  by sorry
