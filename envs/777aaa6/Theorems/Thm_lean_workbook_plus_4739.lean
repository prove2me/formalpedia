-- Prove2me | Theorems.Thm_lean_workbook_plus_4739
-- name    : lean_workbook_plus_4739
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/96b4f939-987b-44c1-885c-5f2322adafdc
-- statement:
--   Let $a$ and $b$ are positive numbers. $$\frac{a}{a^4 +b^2 }+\frac{b}{a^2 +b^4} \le \frac{1}{ab}.$$ Switzerland - Swiss 1998
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4739 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a / (a ^ 4 + b ^ 2) + b / (a ^ 2 + b ^ 4)) ≤ 1 / (a * b)   :=  by sorry
