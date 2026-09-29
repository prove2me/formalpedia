-- Prove2me | Theorems.Thm_lean_workbook_plus_55217
-- name    : lean_workbook_plus_55217
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/85f5ccd1-739d-463c-a1e2-8f3a93d40d2f
-- statement:
--   Prove that \(\frac{3(a^2+b^2+c^2)}{2(ab+bc+ca)}\ge \frac{a}{b+c} + \frac{b}{c+a} + \frac{c}{a+b}\) for positive real numbers \(a, b, c\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55217 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (3 * (a ^ 2 + b ^ 2 + c ^ 2)) / (2 * (a * b + b * c + a * c)) ≥ a / (b + c) + b / (c + a) + c / (a + b)   :=  by sorry
