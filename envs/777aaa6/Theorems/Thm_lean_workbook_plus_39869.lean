-- Prove2me | Theorems.Thm_lean_workbook_plus_39869
-- name    : lean_workbook_plus_39869
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/6aa92a2c-6122-45a1-bcb1-c0f1fd7158d0
-- statement:
--   $\frac{1}{\frac{1}{a}+\frac{1}{b}}+\frac{1}{\frac{1}{c}+\frac{1}{d}} \leq \frac{a+b+c+d}{4}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39869 {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
  1 / (1 / a + 1 / b) + 1 / (1 / c + 1 / d) ≤ (a + b + c + d) / 4   :=  by sorry
