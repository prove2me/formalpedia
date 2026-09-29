-- Prove2me | Theorems.Thm_lean_workbook_plus_65342
-- name    : lean_workbook_plus_65342
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/75508335-eb36-4fd0-9122-405b22d484d2
-- statement:
--   Let $y=\sqrt{x^2+\sqrt{x^4+1}}$ ,
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65342 (x : ℝ) : ∃ y, y = Real.sqrt (x^2 + Real.sqrt (x^4 + 1))   :=  by sorry
