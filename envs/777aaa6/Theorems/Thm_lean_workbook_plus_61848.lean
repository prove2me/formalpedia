-- Prove2me | Theorems.Thm_lean_workbook_plus_61848
-- name    : lean_workbook_plus_61848
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/33175247-3a5d-4bd4-86a3-d6c54bceca15
-- statement:
--   Prove that \(\frac{a+b+c}{b+c} + \frac{b}{c+a} + \frac{c}{a+b} \geq 2\) if \(a, b, c\) are positive.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61848 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) / (b + c) + b / (c + a) + c / (a + b) ≥ 2   :=  by sorry
