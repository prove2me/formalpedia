-- Prove2me | Theorems.Thm_lean_workbook_plus_58893
-- name    : lean_workbook_plus_58893
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/2a4f7220-3d87-42a8-85e2-b651dfa8a5af
-- statement:
--   The sum of an arithmetic sequence with difference 1, 100 terms, and first term x is $ \dfrac{100}{2} (2x + (99)(1)) = 100x + 4950$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58893 (x : ℤ) : ∑ k in Finset.range 100, (x + k) = 100*x + 4950   :=  by sorry
