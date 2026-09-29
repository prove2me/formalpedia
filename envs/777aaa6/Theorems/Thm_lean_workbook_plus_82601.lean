-- Prove2me | Theorems.Thm_lean_workbook_plus_82601
-- name    : lean_workbook_plus_82601
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/c3ec5015-4585-4c9d-ba3c-5c24100d383c
-- statement:
--   We have: $3\geq \frac{1}{x}+\frac{1}{y}+\frac{1}{z}\Rightarrow 3(\frac{1}{x}+\frac{1}{y}+\frac{1}{z})\geq (\frac{1}{x}+\frac{1}{y}+\frac{1}{z})^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82601 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : 3 ≥ 1/x + 1/y + 1/z) : 3 * (1/x + 1/y + 1/z) ≥ (1/x + 1/y + 1/z)^2   :=  by sorry
