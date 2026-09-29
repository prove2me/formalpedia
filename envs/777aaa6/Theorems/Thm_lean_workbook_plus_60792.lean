-- Prove2me | Theorems.Thm_lean_workbook_plus_60792
-- name    : lean_workbook_plus_60792
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/325cdd90-aad0-426d-be41-3b7aeccbaa02
-- statement:
--   substitution $ a = x + y,b = y + z,c = z + x$ \n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60792 (x y z a b c : ℝ) : a = x + y ∧ b = y + z ∧ c = z + x → a + b + c = x + y + z + (x + y + z)   :=  by sorry
