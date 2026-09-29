-- Prove2me | Theorems.Thm_lean_workbook_plus_27087
-- name    : lean_workbook_plus_27087
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/d5583217-d32c-4505-9fe9-8c762a0af2ef
-- statement:
--   For example, $\frac1{(n-1)n(n+1)}=(1/2)\frac1{n-1} + (-1)\frac1n+(1/2)\frac1{n+1}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27087 (n : ℕ) (hn : 1 < n) : (1 : ℝ) / ((n - 1) * n * (n + 1)) = 1 / 2 * (1 / (n - 1)) - 1 * (1 / n) + 1 / 2 * (1 / (n + 1))   :=  by sorry
