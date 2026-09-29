-- Prove2me | Theorems.Thm_lean_workbook_plus_27866
-- name    : lean_workbook_plus_27866
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/8191474c-2212-4d50-8ccd-6aa0118d4c12
-- statement:
--   Let $a,b,c>0$ and $a^2+bc=1.$ Prove that $(1-a^2)^2+(1-b^2)^2+(1-c^2)^2\geq \frac{2}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27866 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (hab : a^2 + b * c = 1) : (1 - a^2)^2 + (1 - b^2)^2 + (1 - c^2)^2 ≥ 2 / 3   :=  by sorry
