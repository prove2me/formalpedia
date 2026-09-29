-- Prove2me | Theorems.Thm_lean_workbook_plus_47929
-- name    : lean_workbook_plus_47929
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/7c271359-7432-4582-93db-3f5acd81ad94
-- statement:
--   $(a-b)^2(a+b) \geq 0 \implies a^3+b^3 \geq a^2b+ab^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47929 (a b : ℝ) : (a - b) ^ 2 * (a + b) ≥ 0 → a ^ 3 + b ^ 3 ≥ a ^ 2 * b + a * b ^ 2   :=  by sorry
