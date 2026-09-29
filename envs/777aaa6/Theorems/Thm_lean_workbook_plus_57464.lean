-- Prove2me | Theorems.Thm_lean_workbook_plus_57464
-- name    : lean_workbook_plus_57464
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/34f6d8f8-0434-4cfb-93cf-b06e2301ae03
-- statement:
--   For positive real numbers $x,y,z$,\n$$\frac{x}{4x+y+z}+\frac{y}{x+4y+z}+\frac{z}{x+y+4z} \leq \frac{1}{2}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57464 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (4 * x + y + z) + y / (x + 4 * y + z) + z / (x + y + 4 * z) ≤ 1 / 2)   :=  by sorry
