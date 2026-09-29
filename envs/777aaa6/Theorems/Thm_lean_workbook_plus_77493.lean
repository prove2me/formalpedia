-- Prove2me | Theorems.Thm_lean_workbook_plus_77493
-- name    : lean_workbook_plus_77493
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/0eaa9a97-5ad7-4ea5-9329-ac7b686204dd
-- statement:
--   Prove: ${(m + n + p)^2} \ge 3(mn + np + mp)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77493 : ∀ m n p : ℝ, (m + n + p) ^ 2 ≥ 3 * (m * n + n * p + m * p)   :=  by sorry
