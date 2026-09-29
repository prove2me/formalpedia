-- Prove2me | Theorems.Thm_lean_workbook_plus_72783
-- name    : lean_workbook_plus_72783
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/9c1f4f1f-5927-4f5d-aab8-502c44bfe18a
-- statement:
--   For a 3 digit number to be divisible by $ 6$ , the 3 digit number should be divisible by both $ 3$ and $ 2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72783 (a b c : ℕ) (h₁ : 1 ≤ a ∧ a ≤ 9) (h₂ : 0 ≤ b ∧ b ≤ 9) (h₃ : 0 ≤ c ∧ c ≤ 9) : a * 100 + b * 10 + c ≡ 0 [ZMOD 6] ↔ a * 100 + b * 10 + c ≡ 0 [ZMOD 3] ∧ a * 100 + b * 10 + c ≡ 0 [ZMOD 2]   :=  by sorry
