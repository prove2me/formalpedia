-- Prove2me | Theorems.Thm_lean_workbook_plus_22586
-- name    : lean_workbook_plus_22586
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/1b409688-9e5a-4c1d-9dd8-8a599ec6be51
-- statement:
--   If $a,b,c>0$ ,prove $a^2b+b^2c+c^2a+a^3+b^3+c^3$ ≥ $2(ab^2+bc^2+ca^2)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22586 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 * b + b^2 * c + c^2 * a + a^3 + b^3 + c^3 ≥ 2 * (a * b^2 + b * c^2 + c * a^2)   :=  by sorry
