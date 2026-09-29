-- Prove2me | Theorems.Thm_lean_workbook_plus_57415
-- name    : lean_workbook_plus_57415
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/843b1dac-3972-4759-b247-84bb420460ca
-- statement:
--   Let $x,y,z$ be nonzero real numbers such that $x+y+z=\frac{1}{x}+\frac{1}{y}+\frac{1}{z}=1$ . Prove that at least one of $x,y,z$ is equal to 1.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57415 (x y z : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x + y + z = 1) (h : 1/x + 1/y + 1/z = 1) : x = 1 ∨ y = 1 ∨ z = 1   :=  by sorry
