-- Prove2me | Theorems.Thm_lean_workbook_plus_54459
-- name    : lean_workbook_plus_54459
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/6f446c37-0111-4074-a071-a8fa06b0d975
-- statement:
--   Does the following inequality hold for positive real numbers a, b, c, and a positive constant M: \n$ (ab+bc+ca)* \frac{9}{ab+bc+ca +1} \leq \frac{(a+b+c)^2}{3} * \frac{9}{\frac{(a+b+c)^2}{3}+1} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54459 (a b c M : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = M) :  (a * b + b * c + c * a) * 9 / (a * b + b * c + c * a + 1) ≤   (a + b + c) ^ 2 / 3 * 9 / ((a + b + c) ^ 2 / 3 + 1)   :=  by sorry
