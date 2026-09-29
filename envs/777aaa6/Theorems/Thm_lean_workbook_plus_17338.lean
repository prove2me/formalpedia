-- Prove2me | Theorems.Thm_lean_workbook_plus_17338
-- name    : lean_workbook_plus_17338
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/58793106-c60b-4881-99a0-46d9ce179bd0
-- statement:
--   Let a, b and c be real numbers. Prove that at least one of $(a+b+c)^2 - 9ab, (a+b+c)^2 - 9bc, (a+b+c)^2 - 9ca$ is non-negative
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17338 (a b c : ℝ) : (a+b+c)^2 - 9*a*b >= 0 ∨ (a+b+c)^2 - 9*b*c >= 0 ∨ (a+b+c)^2 - 9*c*a >= 0   :=  by sorry
