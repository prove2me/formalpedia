-- Prove2me | Theorems.Thm_lean_workbook_plus_23346
-- name    : lean_workbook_plus_23346
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/30c08bb6-8c3f-4e29-b7d1-659352ca2658
-- statement:
--   Given $abc=9!$ and $a\le b\le c$ , then $9!=abc\ge a^3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23346 (a b c : ℕ) (h₁ : a ≤ b ∧ b ≤ c) (h₂ : a * b * c = 9!) : a^3 ≤ 9!   :=  by sorry
