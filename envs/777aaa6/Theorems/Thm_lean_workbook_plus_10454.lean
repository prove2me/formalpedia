-- Prove2me | Theorems.Thm_lean_workbook_plus_10454
-- name    : lean_workbook_plus_10454
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/b7051d01-3027-4738-b45a-e80c80d2fb1e
-- statement:
--   Note that $\sqrt{x^2+1}<x+1$ for $x>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10454 (x : ℝ) (hx : 0 < x) : Real.sqrt (x ^ 2 + 1) < x + 1   :=  by sorry
