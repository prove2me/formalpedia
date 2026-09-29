-- Prove2me | Theorems.Thm_lean_workbook_plus_16687
-- name    : lean_workbook_plus_16687
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/0c71861c-a9f7-45e4-8075-6ea040f088bd
-- statement:
--   This is equivalent to show that $32a^{5}+32a^{4}-16a^{3}-16a^{2}+9a-1\geq 0$ for a $\in$ [0,1]
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16687 : ∀ a ∈ Set.Icc (0:ℝ) 1, 32*a^5 + 32*a^4 - 16*a^3 - 16*a^2 + 9*a - 1 ≥ 0   :=  by sorry
