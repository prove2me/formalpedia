-- Prove2me | Theorems.Thm_lean_workbook_plus_28753
-- name    : lean_workbook_plus_28753
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/bc22b318-1681-43ec-bca1-9b869640eeff
-- statement:
--   Let $ a , b, c \ge 0 $ and $ a+bc=2.$ Prove that $$a^2+b^2+c^2+abc\geq 4 $$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28753 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a + b * c = 2) : a ^ 2 + b ^ 2 + c ^ 2 + a * b * c ≥ 4   :=  by sorry
