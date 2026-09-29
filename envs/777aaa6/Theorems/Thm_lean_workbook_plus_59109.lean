-- Prove2me | Theorems.Thm_lean_workbook_plus_59109
-- name    : lean_workbook_plus_59109
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/b5abe228-aff4-4af4-b5ee-6cb92adc0a40
-- statement:
--   Suppose that $a^2 + b^2 + c^2 = 1$ for positive real numbers $a, b, c$ . Find the minimum possible value of $\frac{ab}{c} + \frac{bc}{a} + \frac{ca}{b}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59109 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : 3 ≤ ab / c + bc / a + ca / b   :=  by sorry
