-- Prove2me | Theorems.Thm_lean_workbook_plus_2811
-- name    : lean_workbook_plus_2811
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/f5b52faf-1e5f-437a-8ab4-490f4346a0ca
-- statement:
--   The equation $x^2+2bx+a=0$ has real roots when $4b^2-4a\ge{0}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2811 (a b : ℝ) (h : 4 * b^2 - 4 * a ≥ 0) : ∃ x, x^2 + 2 * b * x + a = 0   :=  by sorry
