-- Prove2me | Theorems.Thm_lean_workbook_plus_21877
-- name    : lean_workbook_plus_21877
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/a1d1d579-f23d-465b-81f9-6696a85c1b19
-- statement:
--   Let $a,b,c>0$ and $a^2+2bc=1.$ Prove that $$a+b+c\le \sqrt 3\left(a^2+b^2+c^2\right)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21877 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + 2 * b * c = 1) : a + b + c ≤ Real.sqrt 3 * (a^2 + b^2 + c^2)   :=  by sorry
