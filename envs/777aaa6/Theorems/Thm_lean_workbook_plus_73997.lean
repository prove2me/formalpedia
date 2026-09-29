-- Prove2me | Theorems.Thm_lean_workbook_plus_73997
-- name    : lean_workbook_plus_73997
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/1e79c6d9-3d09-4bee-8d90-324199508e20
-- statement:
--   Prove that the equation $a^2-3ab+b^2+1=0$ has infinitely many integer solutions $(a, b)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73997 : ∃ c : ℤ, ∃ d : ℤ, a^2 - 3 * a * b + b^2 + 1 = 0   :=  by sorry
