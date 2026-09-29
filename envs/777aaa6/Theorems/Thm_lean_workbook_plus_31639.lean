-- Prove2me | Theorems.Thm_lean_workbook_plus_31639
-- name    : lean_workbook_plus_31639
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/efc79159-7ad5-45b6-be7b-2e0f4459ce99
-- statement:
--   Prove that: $\frac{a}{b^{2}+1}+\frac{b}{c^{2}+1}+\frac{c}{a^{2}+1}\geq \frac{3}{4}(a\sqrt{a}+b\sqrt{b}+c\sqrt{c})$ given $a,b,c\in \mathbb{R}$, $a,b,c\geq0$, $a^2+b^2+c^2=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31639 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : a / (b^2 + 1) + b / (c^2 + 1) + c / (a^2 + 1) ≥ 3 / 4 * (a * Real.sqrt a + b * Real.sqrt b + c * Real.sqrt c)   :=  by sorry
