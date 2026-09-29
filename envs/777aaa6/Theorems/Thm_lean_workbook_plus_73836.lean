-- Prove2me | Theorems.Thm_lean_workbook_plus_73836
-- name    : lean_workbook_plus_73836
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/4e3ea9dd-fb77-40e0-a356-d98cbac1f984
-- statement:
--   Prove that $\frac{\frac{1}{c}+\frac{1}{a}}{2}\geq\frac{2}{c+a}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73836 {a c : ℝ} (ha : 0 < a) (hc : 0 < c) : (1 / c + 1 / a) / 2 ≥ 2 / (c + a)   :=  by sorry
