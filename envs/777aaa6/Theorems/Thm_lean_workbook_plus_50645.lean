-- Prove2me | Theorems.Thm_lean_workbook_plus_50645
-- name    : lean_workbook_plus_50645
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/74f4594a-bdb1-4755-9488-e25c6a2dd0bd
-- statement:
--   Split the function using partial fractions as $ \frac {x}{(x - 4)(x - 5)} = \frac {5}{x - 5} - \frac {1}{x - 4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50645 (x : ℝ) (hx : x ≠ 4 ∧ x ≠ 5) : x / (x - 4) / (x - 5) = 5 / (x - 5) - 1 / (x - 4)   :=  by sorry
