-- Prove2me | Theorems.Thm_lean_workbook_plus_1961
-- name    : lean_workbook_plus_1961
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/be23944d-62bd-4880-acfa-1f2c4f4f864d
-- statement:
--   Prove the inequality for positive variables a, b, and c: \n$ \frac{a^2}{a+b}+\frac{b^2}{b+c} \ge \frac{3a+2b-c}{4} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1961 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (a + b) + b^2 / (b + c)) ≥ (3 * a + 2 * b - c) / 4   :=  by sorry
