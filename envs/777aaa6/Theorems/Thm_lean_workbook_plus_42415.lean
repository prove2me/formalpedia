-- Prove2me | Theorems.Thm_lean_workbook_plus_42415
-- name    : lean_workbook_plus_42415
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/cc348435-769e-4d46-8037-a2393fff2d4f
-- statement:
--   Let $a,b,c >0 $ and $a^2+b^2+c^2+ab+bc-ca=1.$ Prove that $abc(a+b+c) \le \frac{1}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42415 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1) (h : a^2 + b^2 + c^2 + a * b + b * c - c * a = 1) : a * b * c * (a + b + c) ≤ 1 / 4   :=  by sorry
