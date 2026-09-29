-- Prove2me | Theorems.Thm_lean_workbook_plus_67221
-- name    : lean_workbook_plus_67221
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/f033c8c0-3cde-4697-8f53-1bcd0faf828b
-- statement:
--   Prove that if one of the numbers $25x+31y, 3x+7y$ (where $x,y \in Z$ ) is a multiple of $41$ , then so is the other.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67221 (x y : ℤ) : 41 ∣ (25 * x + 31 * y) ∨ 41 ∣ (3 * x + 7 * y) → 41 ∣ (25 * x + 31 * y) ∧ 41 ∣ (3 * x + 7 * y)   :=  by sorry
