-- Prove2me | Theorems.Thm_lean_workbook_plus_1843
-- name    : lean_workbook_plus_1843
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/e6e6c770-b4b0-4db4-895d-a3ff183d526b
-- statement:
--   sqrt(10*4*3*3) (Heron's formula) -> $6\\sqrt{10}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1843 (a : ℝ) (h : a = 10) : Real.sqrt (10 * 4 * 3 * 3) = 6 * Real.sqrt 10   :=  by sorry
