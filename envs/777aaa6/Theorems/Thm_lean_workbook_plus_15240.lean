-- Prove2me | Theorems.Thm_lean_workbook_plus_15240
-- name    : lean_workbook_plus_15240
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/9e74ba8d-a7e2-4dd5-8ea0-fd12bf7b3a94
-- statement:
--   Let $a,b,c>0$ such that: $a^3 + b^3 + c^3=\frac{1}{9} $ .Prove that $a^2+b^2+c^2+\frac{1}{a^2b^2}+\frac{1}{b^2c^2}+\frac{1}{c^2a^2}\ge\frac{730}{3} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15240 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)(habc : a * b * c = 1) : a^3 + b^3 + c^3 = 1 / 9 → a^2 + b^2 + c^2 + 1 / (a^2 * b^2) + 1 / (b^2 * c^2) + 1 / (c^2 * a^2) ≥ 730 / 3   :=  by sorry
