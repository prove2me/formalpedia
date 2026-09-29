-- Prove2me | Theorems.Thm_lean_workbook_plus_62581
-- name    : lean_workbook_plus_62581
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/2e4cd199-aa4a-4366-8b30-969e5445b861
-- statement:
--   Find the sum of the digits in the base $7$ representation of $6250000$ . Express your answer in base $10$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62581 (a : ℕ) (h : a = 6250000) : (Nat.digits 7 a).sum = 24   :=  by sorry
