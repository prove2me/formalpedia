-- Prove2me | Theorems.Thm_lean_workbook_plus_50239
-- name    : lean_workbook_plus_50239
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/9f528045-0ac2-42d2-a1e5-e0cdb48142e5
-- statement:
--   Given that \(a\) and \(b\) are positive numbers such that \(2a+3b=60\) , find the largest possible value of \(ab\) .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50239 (a b : ℝ) (h : 2*a + 3*b = 60) : a * b ≤ 150   :=  by sorry
