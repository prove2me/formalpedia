-- Prove2me | Theorems.Thm_lean_workbook_plus_14061
-- name    : lean_workbook_plus_14061
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/e27c07ad-837b-4ac1-8be3-7b6da41ffc29
-- statement:
--   Let $a,b$ are positive real number such that $a+b=2.$ Prove that $$\frac{1}{a^2+3}+\frac{1}{b^2+3}\leq \frac{1}{2} $$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14061 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 2) : 1 / (a^2 + 3) + 1 / (b^2 + 3) ≤ 1 / 2   :=  by sorry
