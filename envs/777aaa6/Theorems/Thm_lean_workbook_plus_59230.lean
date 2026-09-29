-- Prove2me | Theorems.Thm_lean_workbook_plus_59230
-- name    : lean_workbook_plus_59230
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/2eff1b86-d3e4-425a-8060-66487cc8d421
-- statement:
--   Prove that $k\cdot \binom{n}{k}=n\cdot \binom{n-1}{k-1}$ using a combinatorial argument.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59230 (n k : ℕ) (h₁ : n ≥ k) (h₂ : k ≥ 1) : n * choose (n - 1) (k - 1) = k * choose n k   :=  by sorry
