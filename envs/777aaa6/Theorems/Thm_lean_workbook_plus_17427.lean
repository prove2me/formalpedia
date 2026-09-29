-- Prove2me | Theorems.Thm_lean_workbook_plus_17427
-- name    : lean_workbook_plus_17427
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/7b542f4a-0193-4f18-b118-da1fcb38d0d8
-- statement:
--   Prove that $\frac{a}{b+c} + \frac{b}{a+c} + \frac{c}{a+b} < 2$ where a,b,c are the sides of a triangle.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17427 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a / (b + c) + b / (a + c) + c / (a + b) < 2   :=  by sorry
