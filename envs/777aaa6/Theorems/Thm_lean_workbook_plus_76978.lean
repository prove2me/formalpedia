-- Prove2me | Theorems.Thm_lean_workbook_plus_76978
-- name    : lean_workbook_plus_76978
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/8c94c41a-be5c-41d0-b83a-7dbbb877e4a0
-- statement:
--   Prove that\n\n$$(1-2a)^2(3a(a-1)^2+8-5a) \geq 0$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76978 : ∀ a : ℝ, (1 - 2 * a) ^ 2 * (3 * a * (a - 1) ^ 2 + 8 - 5 * a) ≥ 0   :=  by sorry
