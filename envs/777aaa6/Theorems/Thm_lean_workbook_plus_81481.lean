-- Prove2me | Theorems.Thm_lean_workbook_plus_81481
-- name    : lean_workbook_plus_81481
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/1b714cc6-3f31-444b-a9a0-676daa667767
-- statement:
--   The equation $x^2+ax+2b = 0$ has real roots when $a^2-8b\ge{0}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81481 (a b : ℝ) (h : a^2 - 8 * b ≥ 0) : ∃ x, x^2 + a * x + 2 * b = 0   :=  by sorry
