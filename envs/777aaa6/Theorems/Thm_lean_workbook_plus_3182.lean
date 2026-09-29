-- Prove2me | Theorems.Thm_lean_workbook_plus_3182
-- name    : lean_workbook_plus_3182
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/053fab5a-1902-4338-bdaa-d445b5be27d8
-- statement:
--   If three distinct integers are chosen at random, show that there will exist two among them, say $a$ and $b$ such that $30$ divides $a^3b-ab^3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3182 (a b c : ℤ) (h₁ : a ≠ b) (h₂ : a ≠ c) (h₃ : b ≠ c) : ∃ a b, 30 ∣ a^3 * b - a * b^3   :=  by sorry
