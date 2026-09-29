-- Prove2me | Theorems.Thm_lean_workbook_plus_49450
-- name    : lean_workbook_plus_49450
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/25462055-1520-4903-95ed-155396b9ba61
-- statement:
--   If $ x+y=4$ and $ xy = 2$ , then find $ x^{6}+y^{6}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49450 (x y : ℝ) (h₁ : x + y = 4) (h₂ : x*y = 2) : x^6 + y^6 = 1584   :=  by sorry
