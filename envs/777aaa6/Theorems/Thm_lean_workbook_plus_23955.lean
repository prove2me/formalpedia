-- Prove2me | Theorems.Thm_lean_workbook_plus_23955
-- name    : lean_workbook_plus_23955
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/4d8806a5-5643-4f4a-ae8c-7a8fed0c5829
-- statement:
--   Prove that $ x^4-40 x^2+64 x+144 > 0 $ for $ x > 2 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23955 (x : ℝ) (hx : x > 2) : x^4 - 40 * x^2 + 64 * x + 144 > 0   :=  by sorry
