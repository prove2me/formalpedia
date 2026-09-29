-- Prove2me | Theorems.Thm_lean_workbook_plus_65093
-- name    : lean_workbook_plus_65093
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/343db81d-7552-4591-8e68-96953dc8c56e
-- statement:
--   $\sum_{k=0}^4 \binom{4+k}{k} \left(\frac14\right)^k\left(\frac34\right)^5$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65093 (k : ℕ) : ∑ k in Finset.range 5, (4 + k).choose k * (1 / 4)^k * (3 / 4)^5 = 1   :=  by sorry
