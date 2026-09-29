-- Prove2me | Theorems.Thm_lean_workbook_plus_69559
-- name    : lean_workbook_plus_69559
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/882ebcfd-2351-4c98-a5c5-dec7d182ffa9
-- statement:
--   Claim 3: $\sum_{k=0}^{n} \binom{n+k}{n} \frac{1}{2^{n+k+1}} = \frac 12$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69559 (n : ℕ) : (∑ k in Finset.range (n+1), ((n + k).choose n) * (1 / (2 ^ (n + k + 1)))) = 1 / 2   :=  by sorry
