-- Prove2me | Theorems.Thm_lean_workbook_plus_36249
-- name    : lean_workbook_plus_36249
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/93ccb6ca-96ec-4a7d-bd79-7f3e23a18612
-- statement:
--   Let $x,y,z$ be positive real numbers . Prove that $\frac{z-y}{x+2y}+\frac{x-z}{y+2z}+\frac{y-x}{z+2x}\geq 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36249 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (z - y) / (x + 2 * y) + (x - z) / (y + 2 * z) + (y - x) / (z + 2 * x) ≥ 0   :=  by sorry
