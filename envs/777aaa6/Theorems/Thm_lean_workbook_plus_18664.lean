-- Prove2me | Theorems.Thm_lean_workbook_plus_18664
-- name    : lean_workbook_plus_18664
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/a4afe46c-73b0-48a1-9e63-6635881a6539
-- statement:
--   Given a,b,c are prositive real numbers ; $ a^2 + b^2 + c^2 = 1$ Find max of P: $ P = \frac {ab}{1 + c^{2}} + \frac {bc}{1 + a^{2}} + \frac {ca}{1 + b^{2}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18664 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : (a * b / (1 + c^2) + b * c / (1 + a^2) + c * a / (1 + b^2)) ≤ 3 / 4   :=  by sorry
