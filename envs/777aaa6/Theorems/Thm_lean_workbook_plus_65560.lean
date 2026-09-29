-- Prove2me | Theorems.Thm_lean_workbook_plus_65560
-- name    : lean_workbook_plus_65560
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/55ee76d3-7635-4215-9067-b6070deb81a0
-- statement:
--   Compute $\sum_{1\le a<b<c\le 7} abc$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65560 (S : Finset ℕ) (hS : S = Finset.Icc 1 7) : ∑ a in S, ∑ b in S, ∑ c in S, a * b * c = 1596   :=  by sorry
