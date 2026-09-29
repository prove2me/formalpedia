-- Prove2me | Theorems.Thm_lean_workbook_plus_50417
-- name    : lean_workbook_plus_50417
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/6f5e7657-bd76-4e8b-8848-16665024064d
-- statement:
--   Let a,b,c >0 satisfy $(1+\frac{a}{b})(1+\frac{b}{c})(1+\frac{c}{a}) = 9$ . Show that $\frac{1}{a}+\frac{1}{b}+\frac{1}{c}=\frac{10}{a+b+c}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50417 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 + a / b) * (1 + b / c) * (1 + c / a) = 9 → 1 / a + 1 / b + 1 / c = 10 / (a + b + c)   :=  by sorry
