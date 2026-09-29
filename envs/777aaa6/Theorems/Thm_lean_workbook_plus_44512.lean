-- Prove2me | Theorems.Thm_lean_workbook_plus_44512
-- name    : lean_workbook_plus_44512
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/0161ca73-36be-4b8a-a18d-bc4c976860df
-- statement:
--   prove that $(\sum a^2)\cdot 3\geq(\sum a)^2$ given $a, b, c$ are positive real numbers
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44512 (a b c : ℝ) : (a^2 + b^2 + c^2) * 3 ≥ (a + b + c)^2   :=  by sorry
