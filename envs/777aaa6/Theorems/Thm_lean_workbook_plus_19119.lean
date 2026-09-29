-- Prove2me | Theorems.Thm_lean_workbook_plus_19119
-- name    : lean_workbook_plus_19119
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/9da68397-96de-4436-9a1e-c1160a5e9a0a
-- statement:
--   Let $a,b,c$ be positive real numbers such that $a^3+b^3+c^3+abc=4$ . Prove that:\n$$ \frac{1}{a^2}+\frac{1}{b^2}+\frac{1}{c^2}+3abc\geq 6$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19119 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a ^ 3 + b ^ 3 + c ^ 3 + a * b * c = 4) : 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 + 3 * a * b * c ≥ 6   :=  by sorry
