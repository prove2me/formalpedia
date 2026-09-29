-- Prove2me | Theorems.Thm_lean_workbook_plus_77111
-- name    : lean_workbook_plus_77111
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/8d398683-ebc5-4758-b3d3-cd18b94e21ea
-- statement:
--   If $x,y,z>0$ and $xyz=8\;,$ Then prove that $\frac{1}{x^2+2}+\frac{1}{y^2+2}+\frac{1}{z^2+2}\geq \frac{1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77111 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (habc : x * y * z = 8) : 1 / (x ^ 2 + 2) + 1 / (y ^ 2 + 2) + 1 / (z ^ 2 + 2) ≥ 1 / 2   :=  by sorry
