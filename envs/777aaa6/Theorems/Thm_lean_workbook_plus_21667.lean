-- Prove2me | Theorems.Thm_lean_workbook_plus_21667
-- name    : lean_workbook_plus_21667
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/6af319d8-fb8e-4c74-ae5e-2da482a546d5
-- statement:
--   Find a polynomial $P(x)$ with real coefficients, such that $P(n)=2^n$ for all $n=0,1,2,...,9$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21667 (x : ℝ) : ∃ P : ℝ → ℝ, (∀ n : ℕ, n < 10 → P n = 2 ^ n)   :=  by sorry
