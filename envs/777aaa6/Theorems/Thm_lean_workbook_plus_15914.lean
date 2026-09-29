-- Prove2me | Theorems.Thm_lean_workbook_plus_15914
-- name    : lean_workbook_plus_15914
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/25cb3732-fee2-45d4-8671-3817108b1fc9
-- statement:
--   Prove that $\sum_{k=1}^{n} k(k+3) = \sum_{k=1}^{n} (k^{2} + 3k)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15914 : ∀ n, ∑ k in Finset.Icc 1 n, (k * (k + 3)) = ∑ k in Finset.Icc 1 n, (k ^ 2 + 3 * k)   :=  by sorry
