-- Prove2me | Theorems.Thm_lean_workbook_plus_44151
-- name    : lean_workbook_plus_44151
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/9c35320d-562f-4f67-b525-0d6622f770d8
-- statement:
--   $ \frac {1}{997} + \frac {1}{998} + ... + \frac {1}{1995} < 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44151 : ∑ k in Finset.Icc (997 : ℕ) 1995, (1 : ℝ) / k < 1   :=  by sorry
