-- Prove2me | Theorems.Thm_lean_workbook_plus_69256
-- name    : lean_workbook_plus_69256
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/663e0e9d-b5f5-4950-83b1-3861ed59ed32
-- statement:
--   Prove the identity: $\sum_{k=0}^{m} {n+k\choose k} = {n+m+1\choose m}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69256 (n m : ℕ) : ∑ k in Finset.range (m+1), choose (n + k) k = choose (n + m + 1) m   :=  by sorry
