-- Prove2me | Theorems.Thm_lean_workbook_plus_62123
-- name    : lean_workbook_plus_62123
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/c4e2b3fc-02c9-4961-a19a-3c12d8f69de6
-- statement:
--   Prove that if $ a,b,c$ are positive real numbers, then:\n\n$ \frac {9}{a + b + c} \le 2 \left( \frac {1}{a + b} + \frac {1}{b + c} + \frac {1}{c + a} \right) \le \frac {1}{a} + \frac {1}{b} + \frac {1}{c}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62123 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (9 / (a + b + c)) ≤ (2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a))) ∧ (2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a))) ≤ (1 / a + 1 / b + 1 / c)   :=  by sorry
