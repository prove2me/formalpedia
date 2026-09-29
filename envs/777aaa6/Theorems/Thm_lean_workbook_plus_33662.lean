-- Prove2me | Theorems.Thm_lean_workbook_plus_33662
-- name    : lean_workbook_plus_33662
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/cb678e9b-4647-4d2f-a8c7-8770c52ccca8
-- statement:
--   Prove that $\frac{1+2a}{1+2a+6a^2}\geq -\frac{48}{49}a+\frac{51}{49}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33662 : ∀ a : ℝ, (1 + 2 * a) / (1 + 2 * a + 6 * a ^ 2) ≥ -(48 / 49) * a + 51 / 49   :=  by sorry
