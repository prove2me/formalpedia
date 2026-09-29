-- Prove2me | Theorems.Thm_lean_workbook_plus_77146
-- name    : lean_workbook_plus_77146
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/9f476901-4a33-4126-9e9e-5e3e6789cdeb
-- statement:
--   If x<0 then $1-x>0$ and $2x^{7}<0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77146 (x : ℝ) (hx : x < 0) : 1 - x > 0 ∧ 2 * x^7 < 0   :=  by sorry
