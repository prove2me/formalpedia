-- Prove2me | Theorems.Thm_lean_workbook_plus_32608
-- name    : lean_workbook_plus_32608
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/dd1be887-5c0b-4a81-b723-496803aa8001
-- statement:
--   Prove the inequality $\frac{a^2}{x}+\frac{b^2}{y}+\frac{c^2}{z}\geq \frac{(a+b+c)^2}{x+y+z}$ using Cauchy-Schwarz inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32608 {a b c x y z : ℝ} (hx : x > 0) (hy : y > 0) (hz : z > 0) : (a^2 / x + b^2 / y + c^2 / z) ≥ (a + b + c)^2 / (x + y + z)   :=  by sorry
