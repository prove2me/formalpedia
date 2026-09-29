-- Prove2me | Theorems.Thm_lean_workbook_plus_31920
-- name    : lean_workbook_plus_31920
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/ed9d76ce-044b-41e4-a4f7-f4eba9cd9ba7
-- statement:
--   $ \arcsin (\sin x) = x, 0 \le x < 2\pi$ , right?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31920 : ∀ x, 0 ≤ x ∧ x < 2 * π → arcsin (sin x) = x   :=  by sorry
