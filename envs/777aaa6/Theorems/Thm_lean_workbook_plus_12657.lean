-- Prove2me | Theorems.Thm_lean_workbook_plus_12657
-- name    : lean_workbook_plus_12657
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/d6247f3a-416b-4e92-8c08-1121d4f52816
-- statement:
--   Find $ \sum^{49}_{k=0} (-1)^k \binom{99}{2k}$ where $ \binom{n}{j} = \frac{n!}{j!(n-j)!}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12657 (n : ℕ) : ∑ k in Finset.range (49+1), (-1 : ℤ)^k * (99 : ℕ).choose (2 * k) = (-1 : ℤ)^49 * 2^49   :=  by sorry
