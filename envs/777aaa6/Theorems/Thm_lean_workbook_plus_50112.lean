-- Prove2me | Theorems.Thm_lean_workbook_plus_50112
-- name    : lean_workbook_plus_50112
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/928e79f3-1577-4dd7-8b91-0ea627d1d8b7
-- statement:
--   If $a$ and $b$ are distinct integers, using the binomial theorem, prove that $a - b$ is a factor of $a^n - b^n$ , whenever \n $n$ is a positive integer.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50112 (a b : ℤ) (n : ℕ) : a - b ∣ a ^ n - b ^ n   :=  by sorry
