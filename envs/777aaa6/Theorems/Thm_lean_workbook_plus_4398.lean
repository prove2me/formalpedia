-- Prove2me | Theorems.Thm_lean_workbook_plus_4398
-- name    : lean_workbook_plus_4398
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/d25d2c01-7140-4ccd-a989-c56239b1f5fa
-- statement:
--   Solve\n\n$ 5x+5y+2xy=-19$ \n\n$ x+y+3xy=-35$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4398 (x y : ℝ) (h₁ : 5*x+5*y+2*x*y=-19) (h₂ : x+y+3*x*y=-35) : x = -3 ∧ y = 4 ∨ x = 4 ∧ y = -3   :=  by sorry
