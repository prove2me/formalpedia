-- Prove2me | Theorems.Thm_lean_workbook_plus_50875
-- name    : lean_workbook_plus_50875
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/c9c14bb2-b21a-459e-bc2a-3e18587ab955
-- statement:
--   Prove that $\frac{1}{1999}<\sum_{n=1}^{999} \frac{2n-1}{2n}<\frac{1}{44}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50875 :
  (1 / (1999 : ℝ)) < ∑ n in (Finset.range 999), ((2 * n - 1) / (2 * n)) ∧
  ∑ n in (Finset.range 999), ((2 * n - 1) / (2 * n)) < (1 / 44)   :=  by sorry
