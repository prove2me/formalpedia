-- Prove2me | Theorems.Thm_lean_workbook_plus_62967
-- name    : lean_workbook_plus_62967
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/0a7cec89-245c-4f3a-839b-050383eabae1
-- statement:
--   Find the values of $k$ that satisfy the equation $(k-{1\over2})(k+2)(k-3)(k+{1\over 3})=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62967 (k : ℝ) : (k - 1 / 2) * (k + 2) * (k - 3) * (k + 1 / 3) = 0 ↔ k = 1 / 2 ∨ k = -2 ∨ k = 3 ∨ k = -1 / 3   :=  by sorry
