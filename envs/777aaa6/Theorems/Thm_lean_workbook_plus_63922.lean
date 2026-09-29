-- Prove2me | Theorems.Thm_lean_workbook_plus_63922
-- name    : lean_workbook_plus_63922
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/c9940f09-e57f-4b92-8116-52c3f0dcdf39
-- statement:
--   Solve the quadratic equation $x^2+6x=3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63922 (x : ℝ) : x^2 + 6*x = 3 ↔ x = -3 + 2*Real.sqrt 3 ∨ x = -3 - 2*Real.sqrt 3   :=  by sorry
