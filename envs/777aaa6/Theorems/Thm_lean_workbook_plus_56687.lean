-- Prove2me | Theorems.Thm_lean_workbook_plus_56687
-- name    : lean_workbook_plus_56687
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/e2be1353-2875-438c-9fa3-cce07247026d
-- statement:
--   Let $a, b$ and $c$ be positive real numbers such that $\frac{a+b}{c} + \frac{b+c}{2a} +\frac{c+a}{b}=\frac{13}{2} .$ Prove that $a \leq b+c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56687 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / c + (b + c) / (2 * a) + (c + a) / b = 13 / 2 → a ≤ b + c   :=  by sorry
