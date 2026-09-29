-- Prove2me | Theorems.Thm_lean_workbook_plus_9393
-- name    : lean_workbook_plus_9393
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/dc6ff6d3-762c-44e5-b535-e1d0bca39b36
-- statement:
--   Telescope the sum: $\sum_{i=1}^{d}\binom{n+i-1}{n}= \sum_{i=1}^{d} \left[\binom{n+i}{n+1} - \binom{n+i-1}{n+1}\right]$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9393 (n d : ℕ) :
  ∑ i in Finset.Icc 1 d, choose (n + i - 1) n =
    ∑ i in Finset.Icc 1 d, (choose (n + i) (n + 1) - choose (n + i - 1) (n + 1))   :=  by sorry
