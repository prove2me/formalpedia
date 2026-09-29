-- Prove2me | Theorems.Thm_lean_workbook_plus_7923
-- name    : lean_workbook_plus_7923
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/03736058-d8ec-4465-b476-c9f3ca2e38c3
-- statement:
--   Prove \\(\\frac{1}{\\frac{1}{1+a}+\\frac{1}{1+b}+\\frac{1}{1+c}}-\\frac{1}{\\frac{1}{a}+\\frac{1}{b}+\\frac{1}{c}}\\geq \\frac{1}{3}\\) for arbitrary positive reals \\(a, b, c.\\) Is there a clean way to solve this problem without expanding?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7923 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c)) - 1 / (1 / a + 1 / b + 1 / c)) ≥ 1 / 3   :=  by sorry
