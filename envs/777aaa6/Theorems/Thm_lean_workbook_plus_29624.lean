-- Prove2me | Theorems.Thm_lean_workbook_plus_29624
-- name    : lean_workbook_plus_29624
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/7081a9f1-8621-4dd2-b9b6-c61d37469813
-- statement:
--   Let $a,b,c\geq \frac{4}{3}.$ Prove that $a+b+c\geq \frac{8}{5}\left( \frac{2}{a}-\frac{1}{b}+ \frac{1}{c}+1\right) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29624 (a b c : ℝ) (ha : 4/3 ≤ a) (hb : 4/3 ≤ b) (hc : 4/3 ≤ c) : a + b + c ≥ (8/5) * (2/a - 1/b + 1/c + 1)   :=  by sorry
