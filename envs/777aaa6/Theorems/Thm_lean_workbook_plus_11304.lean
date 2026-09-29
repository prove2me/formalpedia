-- Prove2me | Theorems.Thm_lean_workbook_plus_11304
-- name    : lean_workbook_plus_11304
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/cd4c9b9b-a5b7-4d12-a082-8fa0942efd48
-- statement:
--   Prove that the sum of the alternating sequence $1-2+3-4+5-6+\dots+2003-2004$ is $-1002$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11304 : ∑ k in Finset.range 2004, (-1 : ℤ)^k * (k + 1) = -1002   :=  by sorry
