-- Prove2me | Theorems.Thm_lean_workbook_plus_38561
-- name    : lean_workbook_plus_38561
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/e4a47d30-c33a-4972-94f9-c1adceb3c48d
-- statement:
--   Let $ a,b,c\ge 0$ such that: \n $ a^2+c^2=1,b^2+2b(a+c)=6$ \nProve that: $ b(a-c)\ge 4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38561 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a^2 + c^2 = 1) (hbc : b^2 + 2 * b * (a + c) = 6) : b * (a - c) ≥ 4   :=  by sorry
