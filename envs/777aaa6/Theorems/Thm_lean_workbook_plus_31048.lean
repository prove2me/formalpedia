-- Prove2me | Theorems.Thm_lean_workbook_plus_31048
-- name    : lean_workbook_plus_31048
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/409bbf7a-1ae7-41dd-a386-1143e33937a1
-- statement:
--   Prove that: $2\sum_{k=1}^{n}\ln{k}{\ge}(n+1)\ln(n+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31048 : ∀ n : ℕ, 2 * ∑ k in Finset.range n, Real.log k ≥ (n + 1) * Real.log (n + 1)   :=  by sorry
