-- Prove2me | Theorems.Thm_lean_workbook_plus_22669
-- name    : lean_workbook_plus_22669
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/12a3a6f0-44b5-4cae-8ce6-e79cbb5a2c6f
-- statement:
--   Given the inequalities $1 - xy \geq 0$, $1 - xz \geq 0$, and $1 - yz \geq 0$, prove that $(1 - xy)(1 - yz)(1 - zx) \geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22669 (x y z : ℝ) (h1 : 1 - x*y ≥ 0) (h2 : 1 - x*z ≥ 0) (h3 : 1 - y*z ≥ 0) : (1 - x*y) * (1 - y*z) * (1 - z*x) ≥ 0   :=  by sorry
