-- Prove2me | Theorems.Thm_lean_workbook_plus_57489
-- name    : lean_workbook_plus_57489
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/400af89c-9e95-46b0-8d21-74a7856ea9c4
-- statement:
--   For $ x+y=0 \implies \sin y = \sin (-x) = -\sin x $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57489 : ∀ x y : ℝ, x + y = 0 → sin y = -sin x   :=  by sorry
