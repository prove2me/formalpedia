-- Prove2me | Theorems.Thm_lean_workbook_plus_46525
-- name    : lean_workbook_plus_46525
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/7256df48-81e7-47fe-a43b-fd8434c364c7
-- statement:
--   Prove the identity: $\sum_{p=1}^{n}\binom{n}{p} = 2^n - 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46525 (n : ℕ) : ∑ p in Finset.Icc 1 n, choose n p = 2^n - 1   :=  by sorry
