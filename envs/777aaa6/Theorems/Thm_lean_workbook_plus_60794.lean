-- Prove2me | Theorems.Thm_lean_workbook_plus_60794
-- name    : lean_workbook_plus_60794
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/8960c792-90e0-4098-8da4-7ec6ef7cb466
-- statement:
--   Now use binomial theorem. Notice that to get the constant term we need $ \displaystyle\sum_{i=0}^{3}\dbinom{10}{3i}\dbinom{10}{i}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60794 :
  ∑ k in Finset.Icc 0 3, (Nat.choose 10 (3 * k) * Nat.choose 10 k) = 1210   :=  by sorry
