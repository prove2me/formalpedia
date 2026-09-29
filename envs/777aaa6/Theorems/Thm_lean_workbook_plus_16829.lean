-- Prove2me | Theorems.Thm_lean_workbook_plus_16829
-- name    : lean_workbook_plus_16829
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/bc76eef4-3058-422c-ad69-36dac6ba4015
-- statement:
--   For all $a,b,c,$ positive real number. Show that $\frac{a}{b}+\frac{b}{c}+\frac{c}{a} \geqslant 3 + \frac{(c-a)^2}{a(b+c)}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16829 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b + b / c + c / a ≥ 3 + (c - a) ^ 2 / (a * (b + c))   :=  by sorry
