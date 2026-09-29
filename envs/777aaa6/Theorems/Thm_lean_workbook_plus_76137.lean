-- Prove2me | Theorems.Thm_lean_workbook_plus_76137
-- name    : lean_workbook_plus_76137
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/6b1950c4-4b4d-4458-8e00-2658f2765bee
-- statement:
--   Suppose $a,b,c$ are the sides of a triangle. Prove or disprove $ a(b+c-a)^2+b(a+c-b)^2+c(a+b-c)^2 \geq 3abc. $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76137 {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a * (b + c - a) ^ 2 + b * (a + c - b) ^ 2 + c * (a + b - c) ^ 2 ≥ 3 * a * b * c   :=  by sorry
