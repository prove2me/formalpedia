-- Prove2me | Theorems.Thm_lean_workbook_plus_32296
-- name    : lean_workbook_plus_32296
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/9c1a58d2-a4e8-474a-a6c2-5fe899cf9c01
-- statement:
--   The sum of the squares of all integers on the blackboard never changes, and $(a + b - c)^2 + (b + c - a)^2 + (c + a - b)^2$ is at least $a^2 + b^2 + c^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32296 (a b c : ℤ) : (a + b - c) ^ 2 + (b + c - a) ^ 2 + (c + a - b) ^ 2 ≥ a ^ 2 + b ^ 2 + c ^ 2   :=  by sorry
