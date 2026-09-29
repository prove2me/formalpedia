-- Prove2me | Theorems.Thm_lean_workbook_plus_346
-- name    : lean_workbook_plus_346
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/772ebb0a-ff41-471a-b3be-b37ad0a1b719
-- statement:
--   Prove that for nonnegative integers n, m, k with m≤ n, the following equality holds: ${\binom{n}{k}}$ ${\binom{k}{m}}$ = ${\binom{n}{m}}$ ${\binom{n-m}{k-m}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_346 (n k m : ℕ) (h₁ : k ≤ n) (h₂ : m ≤ k) : choose n k * choose k m = choose n m * choose (n - m) (k - m)   :=  by sorry
