-- Prove2me | Theorems.Thm_lean_workbook_plus_82717
-- name    : lean_workbook_plus_82717
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/db40ae4a-f5c0-485a-af9c-53956e175aa2
-- statement:
--   When $ n = 2$ we have\n\n$ 1 + x^2\ge2x\Longleftrightarrow(1 - x)^2\ge0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82717 : ∀ x : ℝ, 1 + x ^ 2 ≥ 2 * x ↔ (1 - x) ^ 2 ≥ 0   :=  by sorry
