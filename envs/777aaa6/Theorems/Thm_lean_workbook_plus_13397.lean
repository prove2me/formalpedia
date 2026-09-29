-- Prove2me | Theorems.Thm_lean_workbook_plus_13397
-- name    : lean_workbook_plus_13397
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/41e9b6f9-1748-4c08-8929-1845a3ab37fe
-- statement:
--   Prove that $\boxed{\ \frac 1{64} < \frac 12\cdot\frac 34\cdot\frac 56\cdot\ldots\cdot\frac {2009}{2010} < \frac 1{44}\ }$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13397 : (1 / 64 : ℝ) < ∏ i in Finset.Icc (1 : ℕ) 2009, (i + 1) / (i + 2) ∧ ∏ i in Finset.Icc (1 : ℕ) 2009, (i + 1) / (i + 2) < 1 / 44   :=  by sorry
