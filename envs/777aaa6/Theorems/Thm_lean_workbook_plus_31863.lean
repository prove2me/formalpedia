-- Prove2me | Theorems.Thm_lean_workbook_plus_31863
-- name    : lean_workbook_plus_31863
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/5c37bfc8-1ad6-40fc-ade6-fb107f50367b
-- statement:
--   Express the $n$ th term of the series as a product: $\frac12\prod_{k=2}^n\frac{\sqrt{k-1}}{1+\sqrt{k}}=\frac12\prod_{k=2}^n\frac{\sqrt{1-\frac1k}}{1+\frac1{\sqrt{k}}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31863 (n : ℕ) : (∏ k in Finset.Icc 2 n, (Real.sqrt (k - 1) / (1 + Real.sqrt k))) = ∏ k in Finset.Icc 2 n, (Real.sqrt (1 - 1 / k) / (1 + 1 / Real.sqrt k))   :=  by sorry
