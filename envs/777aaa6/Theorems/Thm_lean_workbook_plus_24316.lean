-- Prove2me | Theorems.Thm_lean_workbook_plus_24316
-- name    : lean_workbook_plus_24316
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/bd8b74bc-62bd-4387-832d-a2e75d197086
-- statement:
--   Let $a,b,c$ be positive real numbers. Prove that ${\left(1+ \frac{2a}{b+c}\right)\left(1+ \frac{2b}{c+a}\right)\left(1+ \frac{2c}{a+b} \right)}\ge 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24316 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (1 + 2 * a / (b + c)) * (1 + 2 * b / (c + a)) * (1 + 2 * c / (a + b)) ≥ 2   :=  by sorry
