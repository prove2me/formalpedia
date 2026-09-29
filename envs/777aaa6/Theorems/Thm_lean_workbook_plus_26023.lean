-- Prove2me | Theorems.Thm_lean_workbook_plus_26023
-- name    : lean_workbook_plus_26023
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/0cdaac00-daf5-4558-84e4-270aea7970fb
-- statement:
--   Prove that for two nonnegative reals $x,y$ we have $\dfrac{x+y}{2} \ge \sqrt{xy}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26023 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : (x + y) / 2 ≥ Real.sqrt (x * y)   :=  by sorry
