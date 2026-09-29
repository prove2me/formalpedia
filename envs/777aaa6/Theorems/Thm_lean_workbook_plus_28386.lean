-- Prove2me | Theorems.Thm_lean_workbook_plus_28386
-- name    : lean_workbook_plus_28386
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/d7183516-f285-4964-a12f-66539ab543ae
-- statement:
--   $(2017\cdot 2018-2016\cdot 2019)x(x-4035)=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28386 (x : ℝ) (h : (2017 * 2018 - 2016 * 2019) * x * (x - 4035) = 0) : x = 0 ∨ x = 4035   :=  by sorry
