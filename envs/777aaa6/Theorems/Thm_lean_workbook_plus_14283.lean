-- Prove2me | Theorems.Thm_lean_workbook_plus_14283
-- name    : lean_workbook_plus_14283
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/06a5da07-56ea-4839-9bce-03093a76c0ad
-- statement:
--   Prove that for every positive integer n the inequality is hold: $1+\dfrac{1}{4}+\dfrac{1}{9} +\cdots+\dfrac{1}{n^2}\le \dfrac{5}{3}-\dfrac{2}{2n+1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14283 (n : ℕ) (hn : 0 < n) : (∑ i in Finset.range n, (1 / (i + 1)^2)) ≤ (5 / 3) - (2 / (2 * n + 1))   :=  by sorry
