-- Prove2me | Theorems.Thm_lean_workbook_plus_81357
-- name    : lean_workbook_plus_81357
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/f852fb6e-e291-432a-a7ef-eb3b099d2d4d
-- statement:
--   By Cauchy–Schwarz inequality, $\frac{(a+1)^2}{(a^2+1)^2}\le\frac{(a+1)^2}{(a+1)(a^3+1)}=\frac{1}{a^2-a+1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81357 : ∀ a : ℝ, (a + 1) ^ 2 / (a ^ 2 + 1) ^ 2 ≤ 1 / (a ^ 2 - a + 1)   :=  by sorry
