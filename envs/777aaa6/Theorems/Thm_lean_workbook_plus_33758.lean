-- Prove2me | Theorems.Thm_lean_workbook_plus_33758
-- name    : lean_workbook_plus_33758
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/89f73a57-319c-481a-a7fc-b3b51c908760
-- statement:
--   Prove by induction that $(x_1+x_2+...+x_n)^2-(x_1^2+3x_2^2+5x_3^2+\cdots+(2\cdot n-1)\cdot x^2_{n})\geq0$ for $n=2023$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33758 (n : ℕ) (x : ℕ → ℕ) : (∑ i in Finset.range n, x i)^2 - ∑ i in Finset.range n, (2 * i - 1) * x i ^ 2 ≥ 0   :=  by sorry
