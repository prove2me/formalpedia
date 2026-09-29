-- Prove2me | Theorems.Thm_lean_workbook_plus_11849
-- name    : lean_workbook_plus_11849
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/4cc87676-f3fc-4cc5-aab8-3b5d9e2e93c6
-- statement:
--   $\frac{2}{a+b}+\frac{2}{a+c}+\frac{2}{b+c} \leq \frac{1}{a}+\frac{1}{b}+\frac{1}{c}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11849 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 / (a + b) + 2 / (a + c) + 2 / (b + c)) ≤ (1 / a + 1 / b + 1 / c)   :=  by sorry
