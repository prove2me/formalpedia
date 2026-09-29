-- Prove2me | Theorems.Thm_lean_workbook_plus_75681
-- name    : lean_workbook_plus_75681
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/d3ec21dd-8cb0-40a3-bb88-766e0baa5780
-- statement:
--   prove that: $a^{a+b}+b^{a+b} \le 1$, given $a,b \geq 0$ and $a+b=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75681 (a b : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hab : a + b = 1) : a^(a + b) + b^(a + b) ≤ 1   :=  by sorry
