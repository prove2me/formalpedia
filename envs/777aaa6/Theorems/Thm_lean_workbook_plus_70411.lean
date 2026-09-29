-- Prove2me | Theorems.Thm_lean_workbook_plus_70411
-- name    : lean_workbook_plus_70411
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/07c6c9c6-a1d9-4abb-a219-7a4c90fe4a26
-- statement:
--   Prove that\n\n$$(1-2a)^2(3a^3-6a^2-2a+8) \geq 0$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70411 : ∀ a : ℝ, (1 - 2 * a) ^ 2 * (3 * a ^ 3 - 6 * a ^ 2 - 2 * a + 8) ≥ 0   :=  by sorry
