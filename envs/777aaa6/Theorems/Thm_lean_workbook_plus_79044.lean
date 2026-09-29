-- Prove2me | Theorems.Thm_lean_workbook_plus_79044
-- name    : lean_workbook_plus_79044
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/f0b89a8d-2d04-41a5-b22f-1e7a971f7928
-- statement:
--   So the sum of the first ten terms of the geometric sequence is $ 1+2+\cdots + 2^9=2^{10}-1=1023$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79044 ∑ k in (Finset.range 10), (2^k) = 2^10 - 1   :=  by sorry
