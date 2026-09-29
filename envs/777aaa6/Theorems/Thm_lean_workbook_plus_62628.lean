-- Prove2me | Theorems.Thm_lean_workbook_plus_62628
-- name    : lean_workbook_plus_62628
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/70e0c1fa-0f2e-4f3b-8bb9-b37eb931e554
-- statement:
--   Prove that $\sum_{i=0}^n\dbinom{n}{i}2^i=3^n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62628 (n : ℕ) : ∑ i in Finset.range (n+1), choose n i * 2 ^ i = 3 ^ n   :=  by sorry
