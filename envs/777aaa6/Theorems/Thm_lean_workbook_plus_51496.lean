-- Prove2me | Theorems.Thm_lean_workbook_plus_51496
-- name    : lean_workbook_plus_51496
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/aa970985-d6d4-4e4a-a7e5-213277221e33
-- statement:
--   Find the value of $x^3(x^3-18)$ if given $x(x-3) = -1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51496 (x : ℝ) (hx : x * (x - 3) = -1) : x ^ 3 * (x ^ 3 - 18) = -1   :=  by sorry
