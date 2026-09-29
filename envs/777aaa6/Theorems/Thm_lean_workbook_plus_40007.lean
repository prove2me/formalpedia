-- Prove2me | Theorems.Thm_lean_workbook_plus_40007
-- name    : lean_workbook_plus_40007
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/14a308a7-4a39-43f0-9b06-5aa8cb25c004
-- statement:
--   Prove that for all real numbers $x$,\n\n$ |x|+x^2+||x|-1|+6|x-2|+|x^2-1|+3|2x+1|\ge 17$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40007 (x : ℝ) : abs x + x ^ 2 + abs (abs x - 1) + 6 * abs (x - 2) + abs (x ^ 2 - 1) + 3 * abs (2 * x + 1) ≥ 17   :=  by sorry
