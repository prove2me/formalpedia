-- Prove2me | Theorems.Thm_lean_workbook_plus_75195
-- name    : lean_workbook_plus_75195
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/8152357c-72de-44f4-82ae-5b370469e02e
-- statement:
--   Positive real numbers $a$ , $b$ , $c$ satisfy $a^2+b^2+c=1.$ Prove that $$\frac{a^2}{1-a^2}+\frac{b^2}{1-b^2}+\frac{c^2}{1-c^2}\geq1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75195 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c = 1) : a^2 / (1 - a^2) + b^2 / (1 - b^2) + c^2 / (1 - c^2) ≥ 1   :=  by sorry
