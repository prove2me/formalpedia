-- Prove2me | Theorems.Thm_lean_workbook_plus_24325
-- name    : lean_workbook_plus_24325
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/4647e892-f5ae-4624-80f4-776c74b3d382
-- statement:
--   Let $a, b, c>0$ and $(a+b)(b+c)(c+a)=a+b+c-1.$ Prove that $abc\leq \frac{5\sqrt 5-9}{54} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24325 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) (habc : a + b + c = 1) : (a + b) * (b + c) * (c + a) = a + b + c - 1 → a * b * c ≤ (5 * Real.sqrt 5 - 9) / 54   :=  by sorry
