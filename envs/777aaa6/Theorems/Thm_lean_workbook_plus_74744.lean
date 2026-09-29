-- Prove2me | Theorems.Thm_lean_workbook_plus_74744
-- name    : lean_workbook_plus_74744
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/f625cc11-af1a-400f-905d-91f2f9468ddc
-- statement:
--   Let $a, b, c$ be denote nonzero real numbers that add up to $ 0.$ Prove that $\frac{a^3+b^3+c^3+a^2-b^2-c^2}{bc}=3a+2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74744 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : a + b + c = 0) : (a^3 + b^3 + c^3 + a^2 - b^2 - c^2) / (b * c) = 3 * a + 2   :=  by sorry
