-- Prove2me | Theorems.Thm_lean_workbook_plus_44343
-- name    : lean_workbook_plus_44343
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/8b3b5c45-eb04-4ca8-9749-be084db66f39
-- statement:
--   Prove that: $1+2(ab+ac+ad+bc+bd+cd)-(a+b+c+d+4abcd)\geq 0$ given $a,b,c,d > 0$ and $a^{2}+b^{2}+c^{2}+d^{2}=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44343 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a + b + c + d = 1) (h : a^2 + b^2 + c^2 + d^2 = 1) :
  1 + 2 * (a * b + a * c + a * d + b * c + b * d + c * d) - (a + b + c + d + 4 * a * b * c * d) ≥ 0   :=  by sorry
