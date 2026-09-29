-- Prove2me | Theorems.Thm_lean_workbook_plus_23108
-- name    : lean_workbook_plus_23108
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/831a669e-0593-40b7-ba61-71a5c0af17d2
-- statement:
--   Let $a,b\geq 0 $ and $ (a^2+2)(a+b^3+1)\leq 9.$ Prove that \n $$a+b\leq 2$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23108 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)  (h : (a^2 + 2) * (a + b^3 + 1) ≤ 9) : a + b ≤ 2   :=  by sorry
