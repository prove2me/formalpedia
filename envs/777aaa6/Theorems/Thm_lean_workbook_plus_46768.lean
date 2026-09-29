-- Prove2me | Theorems.Thm_lean_workbook_plus_46768
-- name    : lean_workbook_plus_46768
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/610545fa-8775-4020-9b5d-6ed65b7f8c23
-- statement:
--   Prove that \\(\\sqrt{x} \\cdot \\sqrt{y} = \\sqrt{xy}\\) for positive real numbers x and y.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46768 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : Real.sqrt x * Real.sqrt y = Real.sqrt (x * y)   :=  by sorry
