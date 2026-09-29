-- Prove2me | Theorems.Thm_lean_workbook_plus_61962
-- name    : lean_workbook_plus_61962
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/09ce1b80-894a-4330-a611-69318bc5e7f7
-- statement:
--   Prove the formula for the arithmetic progression $a + a+p + a+2p + a+3p + ... = a + (n-1)p + a + np = \frac{(n+1)(2a + np)}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61962 (a p n: ℕ) : ∑ k in Finset.range (n+1), (a + k * p) = (n + 1) * (2 * a + n * p) / 2   :=  by sorry
