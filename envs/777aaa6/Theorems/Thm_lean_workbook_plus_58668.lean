-- Prove2me | Theorems.Thm_lean_workbook_plus_58668
-- name    : lean_workbook_plus_58668
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/3fae0f4d-da63-4481-a9d0-79f840ad5ae5
-- statement:
--   Given the identity $\sum_{n=1}^m \frac{n}{(n+1)!}=1-\frac{1}{(m+1)!}$, find the value of the expression when m=30.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58668 : ∑ n in Finset.Icc 1 30, (n/(n+1)!) = 1 - (1/31!)   :=  by sorry
