-- Prove2me | Theorems.Thm_lean_workbook_plus_20208
-- name    : lean_workbook_plus_20208
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/640d727f-5d84-48e4-82e0-6b502ab956a3
-- statement:
--   Let $a,b$ are positive real number such that $a+b=2$ , prove that $\frac{1}{11+a^{2}}+\frac{1}{11+b^{2}}\leqslant \frac{1}{6}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20208 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 2) : 1 / (11 + a^2) + 1 / (11 + b^2) ≤ 1 / 6   :=  by sorry
