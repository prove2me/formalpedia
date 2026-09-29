-- Prove2me | Theorems.Thm_lean_workbook_plus_41586
-- name    : lean_workbook_plus_41586
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/063cc8a5-b28e-47ca-8d2a-43c5bc67ad81
-- statement:
--   Let $a,b,c,d > 0 $ and $ a^2b^2+b^2c^2+c^2d^2+d^2a^2\leq 2(b c+d a) .$ Prove that \n $$ ab-cd \leq1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41586 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (habcd : a * b * c * d = 1) (h : a^2 * b^2 + b^2 * c^2 + c^2 * d^2 + d^2 * a^2 ≤ 2 * (b * c + d * a)) : a * b - c * d ≤ 1   :=  by sorry
