-- Prove2me | Theorems.Thm_lean_workbook_plus_11237
-- name    : lean_workbook_plus_11237
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/89ba9ae9-f4a4-45de-bdac-c7e04663716b
-- statement:
--   Derive $\log_b a = \frac {1} {\log_a b}$ from the change of base formula.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11237 (a b : ℝ) (ha : a > 0) (hb : b > 0) (hab : a ≠ b) : Real.logb b a = 1 / Real.logb a b   :=  by sorry
