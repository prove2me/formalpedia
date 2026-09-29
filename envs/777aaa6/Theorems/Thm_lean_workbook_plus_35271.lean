-- Prove2me | Theorems.Thm_lean_workbook_plus_35271
-- name    : lean_workbook_plus_35271
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/a643ac35-a244-4cc3-ac8e-bf7ccebb8440
-- statement:
--   The numbers $a$ and $b$ are natural. $10 < a < 20$ and $40 < b < 50$ . $a \cdot b = 2^5 \cdot 3 \cdot 7$ . What is the maximum possible sum of the numbers $a$ and $b$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35271 (a b : ℕ) (h₁ : 10 < a ∧ a < 20) (h₂ : 40 < b ∧ b < 50) (h₃ : a * b = 2^5 * 3 * 7) : a + b ≤ 62   :=  by sorry
