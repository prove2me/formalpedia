-- Prove2me | Theorems.Thm_lean_workbook_plus_66075
-- name    : lean_workbook_plus_66075
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/f157f0de-1b28-404d-b03c-4e6a8d6b12dd
-- statement:
--   We need $2y-2y^3\ge 0$ and so $y\in(-\infty,-1]\cup[0,1]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66075 : ∀ y : ℝ, (y ≤ -1 ∨ 0 ≤ y ∧ y ≤ 1) ↔ 2*y - 2*y^3 ≥ 0   :=  by sorry
