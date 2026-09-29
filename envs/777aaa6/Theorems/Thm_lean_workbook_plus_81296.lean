-- Prove2me | Theorems.Thm_lean_workbook_plus_81296
-- name    : lean_workbook_plus_81296
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/702653da-a670-496c-9576-1fdb78229b37
-- statement:
--   Let $x,y,z$ be nonnegative integers that sum to $6$ . Find the maximum value of $xy^2z^3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81296 (x y z : ℕ) (hx : x + y + z = 6) : x * y^2 * z^3 ≤ 108   :=  by sorry
