-- Prove2me | Theorems.Thm_lean_workbook_plus_16812
-- name    : lean_workbook_plus_16812
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/126d776c-adc7-4116-895f-7ade947121d3
-- statement:
--   Prove that for any positive integer $n$, ${(n + 1)^{n + 1}} > {n^n}(2n + 1) > 1 \times 3 \times 5 \times \cdots \times (2n - 1) \times (2n + 1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16812 : ∀ n : ℕ, (n + 1) ^ (n + 1) > n ^ n * (2 * n + 1) ∧ n ^ n * (2 * n + 1) > (∏ i in Finset.range (n + 1), (2 * i + 1))   :=  by sorry
