-- Prove2me | Theorems.Thm_lean_workbook_plus_60906
-- name    : lean_workbook_plus_60906
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/9d370c4a-b2f3-4fb6-a97c-1ebdb2ee86b5
-- statement:
--   Prove that $c=\frac{-2a+4}{a^2+1}$ is non-negative for $0\leq a\leq 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60906 : ∀ a : ℝ, 0 ≤ a ∧ a ≤ 2 → 0 ≤ (-2 * a + 4) / (a ^ 2 + 1)   :=  by sorry
