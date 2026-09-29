-- Prove2me | Theorems.Thm_lean_workbook_plus_27477
-- name    : lean_workbook_plus_27477
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/01c32300-abc5-47fe-b3e5-a5dd54ebccd4
-- statement:
--   Let $a,b\in [0,1]$ . Prove that $\frac{a}{2b+5}+\frac{b}{2a+5}\leq\frac{2}{7}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27477 (a b : ℝ) (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) : a / (2 * b + 5) + b / (2 * a + 5) ≤ 2 / 7   :=  by sorry
