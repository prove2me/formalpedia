-- Prove2me | Theorems.Thm_lean_workbook_plus_54883
-- name    : lean_workbook_plus_54883
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/73398819-f23e-4a6a-a4bb-a28eabe09048
-- statement:
--   Prove that $\frac{a}{3a + b+c} + \frac{b}{3b + a+ c} + \frac{c}{3c + a+ b} \leq \frac{3}{5}$ given $a,b,c > 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54883 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (3 * a + b + c) + b / (3 * b + a + c) + c / (3 * c + a + b) : ℝ) ≤ 3 / 5   :=  by sorry
