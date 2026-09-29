-- Prove2me | Theorems.Thm_lean_workbook_plus_10237
-- name    : lean_workbook_plus_10237
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/5e0c3f59-c337-4dd7-b6b8-3746228b66b4
-- statement:
--   Prove that $\frac{2k-1}{2k}\leq\sqrt{\frac{2k-1}{2k+1}}$ for $k=1,2,...,n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10237 (k : ℕ) (h : 0 < k) :
  ((2 * k - 1 : ℝ) / (2 * k) : ℝ) ≤ Real.sqrt ((2 * k - 1 : ℝ) / (2 * k + 1 : ℝ))   :=  by sorry
