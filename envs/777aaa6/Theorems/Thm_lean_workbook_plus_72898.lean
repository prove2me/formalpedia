-- Prove2me | Theorems.Thm_lean_workbook_plus_72898
-- name    : lean_workbook_plus_72898
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/4a724e26-022e-4f38-b6e7-c075565f384a
-- statement:
--   Prove that if $a, b, c, d$ are positive real numbers, then $(a+b)(c+d) \geq ac + bd$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72898 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a + b) * (c + d) ≥ a * c + b * d   :=  by sorry
