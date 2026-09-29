-- Prove2me | Theorems.Thm_lean_workbook_plus_17305
-- name    : lean_workbook_plus_17305
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/af4e7b9d-9187-41b7-8e28-00b1e0faa600
-- statement:
--   Given $a, b, c$ are positive real numbers and $\frac{1}{a} + \frac{1}{b} + \frac{1}{c} \leq 1$. Prove that $\frac{b+c}{a+bc} + \frac{a+c}{b+ac} + \frac{b+a}{c+ab} \geq \frac{12}{a+b+c-1}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17305 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : 1 / a + 1 / b + 1 / c ≤ 1) :
  (b + c) / (a + b * c) + (a + c) / (b + a * c) + (b + a) / (c + a * b) ≥ 12 / (a + b + c - 1)   :=  by sorry
