-- Prove2me | Theorems.Thm_lean_workbook_plus_47956
-- name    : lean_workbook_plus_47956
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/ec0053dd-79c7-47ff-ae83-03c049b79490
-- statement:
--   Prove that for non-negative numbers $a, b, c, d$, the following inequality holds: $\frac{(a+c)(b+d)(a+b+c+d)}{4} \geq acd + abd + abc + bcd$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47956 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) : (a + c) * (b + d) * (a + b + c + d) / 4 ≥ a * c * d + a * b * d + a * b * c + b * c * d   :=  by sorry
