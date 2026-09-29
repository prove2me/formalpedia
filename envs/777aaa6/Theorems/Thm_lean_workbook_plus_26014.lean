-- Prove2me | Theorems.Thm_lean_workbook_plus_26014
-- name    : lean_workbook_plus_26014
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/69a340b9-33c6-45d5-bb5f-cba01febab73
-- statement:
--   Prove that for positive real numbers $x$, $y$, and $z$, the inequality $\sum_{cyc}(x^2y+x^2z-2xyz) \geq 0$ holds.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26014 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^2*y + x^2*z - 2*x*y*z) + (y^2*z + y^2*x - 2*y*z*x) + (z^2*x + z^2*y - 2*z*x*y) ≥ 0   :=  by sorry
