-- Prove2me | Theorems.Thm_lean_workbook_plus_29213
-- name    : lean_workbook_plus_29213
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/2fb5e8d3-e1f7-4b61-a55e-c6c55d5339b6
-- statement:
--   Note that $a^3=2a-3$ and $a^4=2a^2-3a$ , so $a^3-a^4=-2a^2+5a-3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29213 (a : ℝ) (h : a^3 = 2*a - 3) (h' : a^4 = 2*a^2 - 3*a) : a^3 - a^4 = -2*a^2 + 5*a - 3   :=  by sorry
