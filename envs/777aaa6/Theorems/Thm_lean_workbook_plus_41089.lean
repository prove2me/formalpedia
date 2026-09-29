-- Prove2me | Theorems.Thm_lean_workbook_plus_41089
-- name    : lean_workbook_plus_41089
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/309bc967-fca8-46f5-826b-acecd35bac49
-- statement:
--   For $z = x + iy$, if $|z - 1| < |z + 3|$, then $x > -1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41089 (z : ℂ) (h : ‖z - 1‖ < ‖z + 3‖) : z.re > -1   :=  by sorry
