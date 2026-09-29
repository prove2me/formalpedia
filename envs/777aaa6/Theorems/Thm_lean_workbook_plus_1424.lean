-- Prove2me | Theorems.Thm_lean_workbook_plus_1424
-- name    : lean_workbook_plus_1424
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/f90b3675-6756-4962-9573-0c2616f70832
-- statement:
--   If $a, b,c,d > 0 $ and $ a^2+b^2 \ge c^2+d^2 $ . Prove that : \n $$ \frac{b}{a+c}+\frac{a}{b+d} \geq 1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1424 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (habc : a * b * c > 0) (hcd : c * d * b > 0) (habd : a * b * d > 0) : (a^2 + b^2 ≥ c^2 + d^2) → b / (a + c) + a / (b + d) ≥ 1   :=  by sorry
