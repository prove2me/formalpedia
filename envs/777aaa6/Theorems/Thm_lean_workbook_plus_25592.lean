-- Prove2me | Theorems.Thm_lean_workbook_plus_25592
-- name    : lean_workbook_plus_25592
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/66c5def1-9d92-4e18-bc6d-8fee3fe6f6f0
-- statement:
--   Let $a,b,c$ be positive real numbers. Prove that ${\left( \frac{a}{b+c}+\frac{1}{2} \right)\left( \frac{b}{c+a}+\frac{1}{2} \right)\left( \frac{c}{a+b}+\frac{1}{2} \right)}\ge 1.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25592 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + 1 / 2) * (b / (c + a) + 1 / 2) * (c / (a + b) + 1 / 2) ≥ 1   :=  by sorry
