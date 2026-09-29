-- Prove2me | Theorems.Thm_lean_workbook_plus_77258
-- name    : lean_workbook_plus_77258
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/b1a80865-cd11-4422-a914-096307c4d680
-- statement:
--   Prove that for any real $x\geq1$ and any integer $c\geq1$ , we have $\sum_{0<ix<c}\{ix\}<\frac c2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77258 (x : ℝ) (c : ℕ) (hx : 1 ≤ x) (hc : 1 ≤ c) : ∑ i in Finset.Ico 1 c, (i * x) % 1 < c / 2   :=  by sorry
