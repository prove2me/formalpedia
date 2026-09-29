-- Prove2me | Theorems.Thm_lean_workbook_plus_76048
-- name    : lean_workbook_plus_76048
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/531b082b-184a-43d4-b19b-6f7f7607ae6c
-- statement:
--   Find the value of the following expression. $9\binom{20}{1}+55\binom{20}{2}+50\binom{20}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76048 (h₁ : 1 ≤ 20 ∧ 1 ≤ 9) (h₂ : 2 ≤ 20 ∧ 2 ≤ 55) (h₃ : 3 ≤ 20 ∧ 3 ≤ 50) : 9 * (Nat.choose 20 1) + 55 * (Nat.choose 20 2) + 50 * (Nat.choose 20 3) = 67630   :=  by sorry
