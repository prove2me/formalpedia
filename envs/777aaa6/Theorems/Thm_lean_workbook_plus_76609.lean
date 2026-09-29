-- Prove2me | Theorems.Thm_lean_workbook_plus_76609
-- name    : lean_workbook_plus_76609
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/09a649a7-ed9f-42b5-9100-0abe4058265e
-- statement:
--   Let $a, b$ and $c$ be positive real numbers. Prove that $$ \big(\frac{a}{b+c}+\frac{1}{2}\big) \big(\frac{b}{c+a}+\frac{1}{2}\big) \big(\frac{c}{a+b}+\frac{1}{2}\big)\ge 1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76609 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a / (b + c) + 1 / 2) * (b / (c + a) + 1 / 2) * (c / (a + b) + 1 / 2) ≥ 1   :=  by sorry
