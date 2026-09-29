-- Prove2me | Theorems.Thm_lean_workbook_plus_2131
-- name    : lean_workbook_plus_2131
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/3763819a-c2d6-4789-95d5-16bbd0601599
-- statement:
--   prove: \(a^{2}b^{2}+b^{2}c^{2}+c^{2}a^{2}\leq\frac{(a^{2}+b^{2}+c^{2})^{2}}{3}\) where \(a,b,c > 0\) using the Cauchy-Schwarz inequality
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2131 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 * b^2 + b^2 * c^2 + c^2 * a^2 ≤ (a^2 + b^2 + c^2)^2 / 3   :=  by sorry
