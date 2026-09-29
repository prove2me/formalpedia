-- Prove2me | Theorems.Thm_lean_workbook_plus_1120
-- name    : lean_workbook_plus_1120
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/857619fd-1aac-4c6e-9b18-1996974cdf5d
-- statement:
--   Let $a, b,c>0.$ Prove that\n\n $$\frac{a+k}{b+c+2k} + \frac{b+k}{c+a+2k} +\frac{c+k}{a+b+2k} \geq \frac{3}{2} $$\nWhere $k\geq 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1120 (a b c k : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hk : 0 ≤ k) : (a + k) / (b + c + 2 * k) + (b + k) / (c + a + 2 * k) + (c + k) / (a + b + 2 * k) ≥ 3 / 2   :=  by sorry
