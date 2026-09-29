-- Prove2me | Theorems.Thm_lean_workbook_plus_39310
-- name    : lean_workbook_plus_39310
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/8134326f-767b-4cb0-99cd-2250a23dd491
-- statement:
--   Let $a,b,c>0$ ,.Prove that $ \sum {\frac{{a + b}}{{{c^2} + ab}}} \le \sum {\frac{1}{a}} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39310 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (c ^ 2 + a * b) + (b + c) / (a ^ 2 + b * c) + (c + a) / (b ^ 2 + a * c) ≤ 1 / a + 1 / b + 1 / c   :=  by sorry
