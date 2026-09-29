-- Prove2me | Theorems.Thm_lean_workbook_plus_49880
-- name    : lean_workbook_plus_49880
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/fd3f0d57-5fca-4bb4-be27-0793d3e37c4b
-- statement:
--   Expand and simplify $(x + n + a)^2$ to show the equality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49880 (x n a : ℤ) : (x + n + a)^2 = (x + n)^2 + 2 * (x + n) * a + a^2   :=  by sorry
