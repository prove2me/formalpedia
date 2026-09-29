-- Prove2me | Theorems.Thm_lean_workbook_plus_55967
-- name    : lean_workbook_plus_55967
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/f6c1d443-e70a-473c-8eb9-7a346862674d
-- statement:
--   Let $a,b,c\ge 0$ . Prove $\frac{1}{2+a}+\frac{1}{2+b}+\frac{1}{2+c}\le 1+\frac{1}{2+a+b+c}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55967 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (1 / (2 + a) + 1 / (2 + b) + 1 / (2 + c)) ≤ (1 + 1 / (2 + a + b + c))   :=  by sorry
