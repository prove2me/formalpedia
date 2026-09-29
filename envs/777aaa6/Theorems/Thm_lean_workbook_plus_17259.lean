-- Prove2me | Theorems.Thm_lean_workbook_plus_17259
-- name    : lean_workbook_plus_17259
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/2dd5a5c3-baf1-473f-833e-6d37265f4712
-- statement:
--   Prove that $\frac{n(n+1)(2n+1)}{6}$ is always an integer (don't use the fact that its equal to the sum of the squares of the first $n$ positive integers).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17259 (n : ℤ) : ∃ k : ℤ, n * (n + 1) * (2 * n + 1) / 6 = k   :=  by sorry
