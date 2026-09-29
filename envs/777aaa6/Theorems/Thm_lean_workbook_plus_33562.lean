-- Prove2me | Theorems.Thm_lean_workbook_plus_33562
-- name    : lean_workbook_plus_33562
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/452e098b-8def-4a6d-90cc-d85c602277f7
-- statement:
--   If $a, b, c>0, ab+bc+ca=1$ prove or disprove that $\frac{a^2b}{a^2b+a+b}+\frac{b^2c}{b^2c+b+c}+\frac{c^2a}{c^2a+c+a}\le\frac{a^2+b^2+c^2}{7\sqrt{3}abc}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33562 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : a * b + b * c + c * a = 1 → a^2 * b / (a^2 * b + a + b) + b^2 * c / (b^2 * c + b + c) + c^2 * a / (c^2 * a + c + a) ≤ (a^2 + b^2 + c^2) / (7 * Real.sqrt 3 * a * b * c)   :=  by sorry
