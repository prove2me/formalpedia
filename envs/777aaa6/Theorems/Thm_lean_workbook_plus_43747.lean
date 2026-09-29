-- Prove2me | Theorems.Thm_lean_workbook_plus_43747
-- name    : lean_workbook_plus_43747
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/f20b10b1-e7b6-4c43-a080-a7504c0524d5
-- statement:
--   If $a$ and $b$ are positive integers such that $a \cdot b = 2400,$ find the least possible value of $a + b.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43747 (∀ a b : ℕ, a * b = 2400 → a + b <= 98) ∧ (∃ a b : ℕ, a * b = 2400 ∧ a + b = 98)  :=  by sorry
