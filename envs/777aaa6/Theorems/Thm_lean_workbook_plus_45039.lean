-- Prove2me | Theorems.Thm_lean_workbook_plus_45039
-- name    : lean_workbook_plus_45039
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/cd7a7ab5-68f9-48fc-9b33-75e3c163c65b
-- statement:
--   Prove that $\sqrt{x}+\sqrt{y} \ge \sqrt{x+y}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45039 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : √x + √y ≥ √(x + y)   :=  by sorry
