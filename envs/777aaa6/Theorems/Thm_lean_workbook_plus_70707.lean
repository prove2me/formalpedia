-- Prove2me | Theorems.Thm_lean_workbook_plus_70707
-- name    : lean_workbook_plus_70707
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/be371c69-b762-48db-8be7-6295711e9679
-- statement:
--   Is it true that $\sqrt{(x-1)^2} = x-1$ for all real values of x?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70707 : ∀ x : ℝ, Real.sqrt ((x-1)^2) = x-1   :=  by sorry
