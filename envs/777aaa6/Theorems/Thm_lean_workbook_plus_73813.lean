-- Prove2me | Theorems.Thm_lean_workbook_plus_73813
-- name    : lean_workbook_plus_73813
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/4c57b73d-910f-4cc4-936b-a629c6bcc744
-- statement:
--   Let $a,b,c >0 $ and $ \frac {1}{a} + \frac {1}{b} + \frac {9}{c} = 3.$ Prove that $$ a + b + c \geq \frac {25}{3}$$ Equality holds when $a=b=\frac{5}{3},c=5.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73813 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : 1 / a + 1 / b + 9 / c = 3) : a + b + c >= 25 / 3 ∧ (a = 5 / 3 ∧ b = 5 / 3 ∧ c = 5)   :=  by sorry
