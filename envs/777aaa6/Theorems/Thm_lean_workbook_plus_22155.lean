-- Prove2me | Theorems.Thm_lean_workbook_plus_22155
-- name    : lean_workbook_plus_22155
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/723a65d9-1f46-4bdb-beba-f2c64403be13
-- statement:
--   If $b|a$ , then $a=kb$ for some positive integer $k$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22155 (a b : ℕ) (h₁ : b ≠ 0) (h₂ : a ≠ 0) : b ∣ a ↔ ∃ k : ℕ, a = k * b   :=  by sorry
