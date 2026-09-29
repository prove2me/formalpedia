-- Prove2me | Theorems.Thm_lean_workbook_plus_58729
-- name    : lean_workbook_plus_58729
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/2bdc2b86-e76c-46f9-a2f6-05046072a602
-- statement:
--   Find the $\sum_{k=0}^{49}{(-1)^k\binom{99}{2k}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58729 (n : ℕ) : ∑ k in Finset.range (49+1), (-1 : ℤ)^k * (99).choose (2 * k) = (-1 : ℤ)^49 * 2^49   :=  by sorry
