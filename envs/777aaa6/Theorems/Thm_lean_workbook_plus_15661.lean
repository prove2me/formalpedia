-- Prove2me | Theorems.Thm_lean_workbook_plus_15661
-- name    : lean_workbook_plus_15661
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/0bab29ec-ba32-42dc-ab0f-e7fd08b00b8d
-- statement:
--   Every integer $287 \le M \le 442$ is good.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15661 (M : ℤ) (h₁ : 287 ≤ M) (h₂ : M ≤ 442) : ¬ M = 0   :=  by sorry
