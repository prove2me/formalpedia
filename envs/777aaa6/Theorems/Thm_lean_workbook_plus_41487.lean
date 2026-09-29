-- Prove2me | Theorems.Thm_lean_workbook_plus_41487
-- name    : lean_workbook_plus_41487
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/8a82b383-f916-46d1-8453-e2e70f4f6ce0
-- statement:
--   Assume that $x_2=x_3=...=x_{2015}=0$ and $x_{1}=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41487 : ∃ x : ℕ → ℝ, x 2 = 0 ∧ x 3 = 0 ∧ x 2015 = 0 ∧ x 1 = 1   :=  by sorry
