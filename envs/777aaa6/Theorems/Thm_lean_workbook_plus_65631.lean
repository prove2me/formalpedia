-- Prove2me | Theorems.Thm_lean_workbook_plus_65631
-- name    : lean_workbook_plus_65631
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/6814cd70-9d09-4df4-8026-101cf549de26
-- statement:
--   So $k^3<61$ and so $k\in\{1,2,3\}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65631 : ∀ k : ℕ, k^3 < 61 → k ∈ ({1, 2, 3} : Finset ℕ)   :=  by sorry
