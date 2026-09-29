-- Prove2me | Theorems.Thm_lean_workbook_plus_34650
-- name    : lean_workbook_plus_34650
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/b03c1f8a-19c5-4450-89a7-57785edb6ff9
-- statement:
--   $$ \left (a+\frac {1}{a+4}\right)\left ( b+\frac {9}{b}\right)\left (c+\frac {1}{c+4}\right) > 3$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34650 : ∀ a b c : ℝ, (a + 1 / (a + 4)) * (b + 9 / b) * (c + 1 / (c + 4)) > 3   :=  by sorry
