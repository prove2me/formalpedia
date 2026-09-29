-- Prove2me | Theorems.Thm_lean_workbook_plus_41962
-- name    : lean_workbook_plus_41962
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/2d37a819-b00c-46b9-b199-d04916d5019a
-- statement:
--   $\frac{1}{x}+\frac{1}{y} \geq \frac{4}{x+y}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41962 (x y : ℝ) (hx : x > 0) (hy : y > 0) : 1/x + 1/y ≥ 4/(x + y)   :=  by sorry
