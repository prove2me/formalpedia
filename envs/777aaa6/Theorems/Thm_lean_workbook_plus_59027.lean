-- Prove2me | Theorems.Thm_lean_workbook_plus_59027
-- name    : lean_workbook_plus_59027
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/b7e7ad46-715a-4e0b-883f-d81e02f6a73d
-- statement:
--   Let $a,b,c\geq \frac{4}{3}.$ Prove that $a+b+c\geq \frac{8}{5}\left( \frac{2}{a}-\frac{1}{b}+ \frac{1}{c}+1\right) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59027 (a b c : ℝ) (ha : 4/3 ≤ a) (hb : 4/3 ≤ b) (hc : 4/3 ≤ c) : a + b + c ≥ 8/5 * (2/a - 1/b + 1/c + 1)   :=  by sorry
