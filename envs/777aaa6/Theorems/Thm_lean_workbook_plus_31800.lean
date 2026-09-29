-- Prove2me | Theorems.Thm_lean_workbook_plus_31800
-- name    : lean_workbook_plus_31800
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/7b723ae1-39da-4ed8-913f-353bffa5c65e
-- statement:
--   Calculate the sum $\sum_{k=0}^{5}\binom{5}{k} \cdot 2^k \cdot (5-k)^{5-k}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31800 (h₁ : 0 < 5) : ∑ k in Finset.range 5, (Nat.choose 5 k) * 2^k * (5 - k)^(5 - k) = 7165   :=  by sorry
