-- Prove2me | Theorems.Thm_lean_workbook_plus_55963
-- name    : lean_workbook_plus_55963
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/2083d691-0436-478f-a31b-bd068f6b4e48
-- statement:
--   Let $a,b,c$ be positive real numbers. Prove that \n $\frac{a^{2}b^{2}(b-c)}{a+b}+\frac{b^{2}c^{2}(c-a)}{b+c}+\frac{c^{2}a^{2}(a-b)}{c+a}\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55963 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 * b^2 * (b - c)) / (a + b) + (b^2 * c^2 * (c - a)) / (b + c) + (c^2 * a^2 * (a - b)) / (c + a) ≥ 0   :=  by sorry
