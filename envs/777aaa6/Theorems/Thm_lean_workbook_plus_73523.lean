-- Prove2me | Theorems.Thm_lean_workbook_plus_73523
-- name    : lean_workbook_plus_73523
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/c6216fe8-7f2c-4cf8-85c3-022079586eee
-- statement:
--   Prove that $(z^m-y^m)(z^m+y^m) = z^(2m)-y^(2m)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73523 (z y : ℂ) (m : ℕ) : (z^m - y^m) * (z^m + y^m) = z^(2*m) - y^(2*m)   :=  by sorry
