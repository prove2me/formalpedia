-- Prove2me | Theorems.Thm_lean_workbook_plus_32901
-- name    : lean_workbook_plus_32901
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/983895c0-13ff-43bb-96ef-5e4a6aacf215
-- statement:
--   $ (k-1)k(k+1)(k+2) = ({k}^{3}-k)(k+2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32901 : ∀ k : ℤ, (k - 1) * k * (k + 1) * (k + 2) = (k ^ 3 - k) * (k + 2)   :=  by sorry
