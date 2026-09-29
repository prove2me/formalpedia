-- Prove2me | Theorems.Thm_lean_workbook_plus_29192
-- name    : lean_workbook_plus_29192
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/bd4b8344-471e-4dec-a401-6fa8a6714a81
-- statement:
--   Prove that $y^4+y^3+y^2+y+1$ is odd for all integers $y$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29192 : ∀ y : ℤ, Odd (y^4 + y^3 + y^2 + y + 1)   :=  by sorry
