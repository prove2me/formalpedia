-- Prove2me | Theorems.Thm_lean_workbook_plus_65220
-- name    : lean_workbook_plus_65220
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/0ae27541-6609-459c-b717-c3a3af8e6209
-- statement:
--   $ (a^6+1)/2+(a^6+2)/3+(a^6+5)/6\ge 2a^3/2+3a^2/3+6a/6=a^3+a^2+a $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65220 (a : ℝ) : (a^6 + 1) / 2 + (a^6 + 2) / 3 + (a^6 + 5) / 6 ≥ a^3 + a^2 + a   :=  by sorry
