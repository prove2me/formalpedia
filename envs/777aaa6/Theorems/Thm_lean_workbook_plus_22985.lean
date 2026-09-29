-- Prove2me | Theorems.Thm_lean_workbook_plus_22985
-- name    : lean_workbook_plus_22985
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/57b36c6c-3db9-486e-94da-4b958b3d1737
-- statement:
--   Prove that $\\dfrac{1}{1993}\\left(1-\\dfrac{1}{6\\cdot 1993^2}\\right)>\\dfrac{1}{1994}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22985 : (1 : ℝ) / 1993 * (1 - 1 / (6 * 1993^2)) > 1 / 1994   :=  by sorry
