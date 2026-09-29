-- Prove2me | Theorems.Thm_lean_workbook_plus_60118
-- name    : lean_workbook_plus_60118
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/50b496cd-745d-41c2-84c6-e221c3cf3875
-- statement:
--   Prove the equation for the real part of the product of two complex numbers: $(a + bi)(c + di) = (ac - bd) + i(ad + bc)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60118 (a b c d : ℝ) : (a + b * Complex.I) * (c + d * Complex.I) = (a * c - b * d) + (a * d + b * c) * Complex.I   :=  by sorry
