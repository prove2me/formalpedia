-- Prove2me | Theorems.Thm_lean_workbook_plus_44040
-- name    : lean_workbook_plus_44040
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/61c13018-ef4a-4700-89f6-e08a25c1ce14
-- statement:
--   $\frac{x}{y}<\frac{x+z}{y+z}$ for $x,y,z\in\mathbb{R}^{+}$ and $x<y$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44040 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxy : x < y) : x / y < (x + z) / (y + z)   :=  by sorry
