-- Prove2me | Theorems.Thm_lean_workbook_plus_42652
-- name    : lean_workbook_plus_42652
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/fca3fbbb-92cc-4064-8a99-ebe9ef30cacb
-- statement:
--   From AM-GM, we have $\frac{x^2+y^2}{2} \ge \sqrt{x^2 y^2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42652 (x y : ℝ) : (x ^ 2 + y ^ 2) / 2 ≥ Real.sqrt (x ^ 2 * y ^ 2)   :=  by sorry
