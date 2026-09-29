-- Prove2me | Theorems.Thm_lean_workbook_plus_40264
-- name    : lean_workbook_plus_40264
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/6b4cef81-7c4e-46d2-a956-5526ce98013d
-- statement:
--   Let $a, b, c$ be denote nonzero real numbers that add up to $ 0.$ Prove that $\frac{a^3+b^3+c^3+a^2-b^2-c^2}{bc}=3a+2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40264 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (habc : a + b + c = 0) : (a^3 + b^3 + c^3 + a^2 - b^2 - c^2) / (b * c) = 3 * a + 2   :=  by sorry
