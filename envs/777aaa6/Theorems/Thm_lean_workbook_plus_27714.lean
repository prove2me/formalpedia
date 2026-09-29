-- Prove2me | Theorems.Thm_lean_workbook_plus_27714
-- name    : lean_workbook_plus_27714
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/f4a6d1ab-dd22-48db-a9f7-7fcc15606f0c
-- statement:
--   Prove that $x^3 - x^2 + x - 1 > 0$ for $ x > 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27714 (x : ℝ) (hx : 1 < x) : x^3 - x^2 + x - 1 > 0   :=  by sorry
