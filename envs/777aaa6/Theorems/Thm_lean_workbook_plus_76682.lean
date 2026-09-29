-- Prove2me | Theorems.Thm_lean_workbook_plus_76682
-- name    : lean_workbook_plus_76682
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/bf779500-f85d-4350-9449-6cf83da3dfb1
-- statement:
--   Let $a,b,c$ be sides of triangle. Prove that $\dfrac{(a+b)(b+c)(c+a)}{8} \ge \dfrac{(2a+b)(2b+c)(2c+a)}{27}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76682 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (a + b) * (b + c) * (c + a) / 8 ≥ (2 * a + b) * (2 * b + c) * (2 * c + a) / 27   :=  by sorry
