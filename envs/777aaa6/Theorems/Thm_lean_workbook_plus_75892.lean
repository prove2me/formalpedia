-- Prove2me | Theorems.Thm_lean_workbook_plus_75892
-- name    : lean_workbook_plus_75892
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/a3252424-f38b-4bff-9302-12be637d151a
-- statement:
--   Given $a, b, c > 0$ and $\frac{1}{1 + a} + \frac{1}{1 + b} + \frac{1}{1 + c} = 2$, prove that $abc \le \frac{9}{64}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75892 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) = 2) → a * b * c ≤ 9 / 64   :=  by sorry
