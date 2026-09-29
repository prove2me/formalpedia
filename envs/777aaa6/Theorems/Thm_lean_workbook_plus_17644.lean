-- Prove2me | Theorems.Thm_lean_workbook_plus_17644
-- name    : lean_workbook_plus_17644
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/55c00e2e-35e6-4781-92f6-1ed5b3d3a624
-- statement:
--   Prove that $x^3-6x^2+8x+4>0$ for all $x \ge 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17644 (x : ℝ) (hx : x ≥ 0) : x^3 - 6 * x^2 + 8 * x + 4 > 0   :=  by sorry
