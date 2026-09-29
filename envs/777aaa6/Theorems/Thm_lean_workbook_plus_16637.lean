-- Prove2me | Theorems.Thm_lean_workbook_plus_16637
-- name    : lean_workbook_plus_16637
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/58620591-4ecc-4cbb-b713-e96c86b838db
-- statement:
--   Let $ a,b,c$ be positive real numbers. Prove that $ \frac {a}{b} + \frac {b}{c} + \frac {c}{a} \ge \frac {a + b}{b + c} + \frac {b + c}{a + b} + 1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16637 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b + b / c + c / a ≥ (a + b) / (b + c) + (b + c) / (a + b) + 1   :=  by sorry
