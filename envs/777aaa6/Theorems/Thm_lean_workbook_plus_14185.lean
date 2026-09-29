-- Prove2me | Theorems.Thm_lean_workbook_plus_14185
-- name    : lean_workbook_plus_14185
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/c1b512d3-75a7-4d26-99f7-b5599b42c3d3
-- statement:
--   Prove that \(\binom{2n}{2} = 2\binom{n}{2} + n^2\) combinatorially.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14185 (n : ℕ) : choose (2 * n) 2 = 2 * choose n 2 + n^2   :=  by sorry
