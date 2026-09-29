-- Prove2me | Theorems.Thm_lean_workbook_plus_64850
-- name    : lean_workbook_plus_64850
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/417fadb9-fbd4-48d2-8f94-907a82a38040
-- statement:
--   Prove that $(ab - 1)(ac - 1)(bc - 1)\geq (a^{2} - 1)(b^{2} - 1)(c^{2} - 1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64850 : ∀ a b c : ℝ, (a * b - 1) * (a * c - 1) * (b * c - 1) ≥ (a ^ 2 - 1) * (b ^ 2 - 1) * (c ^ 2 - 1)   :=  by sorry
