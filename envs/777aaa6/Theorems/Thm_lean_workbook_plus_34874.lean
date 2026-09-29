-- Prove2me | Theorems.Thm_lean_workbook_plus_34874
-- name    : lean_workbook_plus_34874
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/0a179518-1337-4d0b-a900-a2c9035636d5
-- statement:
--   Prove the identity $ \sum_{k = 1}^n k(k - 1) = \frac {(n + 1)n(n - 1)}{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34874 : ∀ n, ∑ k in Finset.range n, k * (k - 1) = (n + 1) * n * (n - 1) / 3   :=  by sorry
