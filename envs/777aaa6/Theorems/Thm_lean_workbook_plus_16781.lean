-- Prove2me | Theorems.Thm_lean_workbook_plus_16781
-- name    : lean_workbook_plus_16781
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/29100055-4fa4-4371-8d03-2f6a1cf7832b
-- statement:
--   If $n$ is even, say $n=2m$ , then $a^n=(a^m)^2 \geq 0$ because squares of real numbers are always nonnegative.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16781 (a : ℝ) (n : ℤ) : n % 2 = 0 → a ^ n ≥ 0   :=  by sorry
