-- Prove2me | Theorems.Thm_lean_workbook_plus_70495
-- name    : lean_workbook_plus_70495
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/ab615822-0c12-4b5e-90b7-a3d1517274a5
-- statement:
--   Prove or disprove , for all $1\geq a\geq b\geq 0$ we've $2a^2(1-b)\geq (a-b)(a^2-b^2+2b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70495 (a b : ℝ) (ha : 1 ≥ a ∧ a ≥ b ∧ b ≥ 0) : 2 * a ^ 2 * (1 - b) ≥ (a - b) * (a ^ 2 - b ^ 2 + 2 * b)   :=  by sorry
