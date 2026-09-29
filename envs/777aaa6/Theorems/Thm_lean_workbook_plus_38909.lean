-- Prove2me | Theorems.Thm_lean_workbook_plus_38909
-- name    : lean_workbook_plus_38909
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/0f62dab7-17ff-4947-bf63-4c3dec151bb8
-- statement:
--   Prove that $2[x]\\leq[2x],$ for all $x > 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38909 (x : ℝ) (hx : 0 < x) : 2 * Int.floor x ≤ Int.floor (2 * x)   :=  by sorry
