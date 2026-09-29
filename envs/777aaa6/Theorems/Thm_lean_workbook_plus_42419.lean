-- Prove2me | Theorems.Thm_lean_workbook_plus_42419
-- name    : lean_workbook_plus_42419
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/ef34c46e-8147-46a1-8e2c-a712cae168b9
-- statement:
--   Prove the identity: $\sum_{k=1}^{n}(k-2)(k+2) = \left(\sum_{k=1}^{n}k^{2}\right)-4n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42419 : ∀ n, ∑ k in Finset.Icc 1 n, (k - 2) * (k + 2) = (∑ k in Finset.Icc 1 n, k ^ 2) - 4 * n   :=  by sorry
