-- Prove2me | Theorems.Thm_lean_workbook_plus_836
-- name    : lean_workbook_plus_836
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/4e2b8ff4-83ab-43a4-85c5-473c41d8e968
-- statement:
--   Prove $ A^3+B^3+C^3-3ABC=(A+B+C)(A^2+B^2+C^2-AB-BC-CA)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_836 : ∀ a b c : ℂ, a^3 + b^3 + c^3 - 3 * a * b * c = (a + b + c) * (a^2 + b^2 + c^2 - a * b - b * c - c * a)   :=  by sorry
