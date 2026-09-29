-- Prove2me | Theorems.Thm_lean_workbook_plus_23656
-- name    : lean_workbook_plus_23656
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/3297ead8-b2d5-4bb4-9d89-f05593d26b4f
-- statement:
--   Let $a, b, c$ three positive real numbers. Prove the following inequality\n\n$ \frac{b+c}{a}+\frac{c+a}{b}+\frac{a+b}{c}\geq 3+\frac{(a^{2}+b^{2}+c^{2})(ab+bc+ca)}{abc(a+b+c)}. $\n\nCezar Lupu
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23656 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c) / a + (c + a) / b + (a + b) / c ≥ 3 + (a^2 + b^2 + c^2) * (a * b + b * c + c * a) / (a * b * c * (a + b + c))   :=  by sorry
