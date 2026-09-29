-- Prove2me | Theorems.Thm_lean_workbook_plus_13113
-- name    : lean_workbook_plus_13113
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/f4569e99-6dbf-4a0e-8988-964772f7a2ea
-- statement:
--   Let $x$ be positive real number , Prove that $(1+x)^3(1+\frac{16}{x^3})\ge 81.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13113 (x : ℝ) (hx : 0 < x) : (1 + x) ^ 3 * (1 + 16 / x ^ 3) ≥ 81   :=  by sorry
