-- Prove2me | Theorems.Thm_lean_workbook_plus_65673
-- name    : lean_workbook_plus_65673
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/ee24fc02-402d-4e8c-895b-07e12f20ad1d
-- statement:
--   If $a, b, c$ are positive reals, prove: $a^3 + b^3 \geq a^2b + b^2a$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65673 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) : a^3 + b^3 ≥ a^2 * b + b^2 * a   :=  by sorry
