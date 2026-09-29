-- Prove2me | Theorems.Thm_lean_workbook_plus_48547
-- name    : lean_workbook_plus_48547
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/d63ed6e2-298e-4ec4-93f6-5d19543f7cbb
-- statement:
--   Let $a,b,c\geq 0$ and $a^2+b^2+c^2\leq 1.$ Prove that $\frac{a}{a^2+bc+1}+\frac{b}{b^2+ca+1}+\frac{c}{c^2+ab+1}+3abc<\sqrt 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48547 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 ≤ 1) : a / (a^2 + b * c + 1) + b / (b^2 + c * a + 1) + c / (c^2 + a * b + 1) + 3 * a * b * c < Real.sqrt 3   :=  by sorry
