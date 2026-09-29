-- Prove2me | Theorems.Thm_lean_workbook_plus_58507
-- name    : lean_workbook_plus_58507
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/aaa33d83-f2b1-4ccb-84c6-445907687ea5
-- statement:
--   $\frac 12(\sqrt{\frac 53}-1)^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58507 (x : ℝ) (hx : x = (5/3 : ℝ)^(1/2) - 1) : (1/2)*x^3 = (1/2)*((5/3 : ℝ)^(1/2) - 1)^3   :=  by sorry
