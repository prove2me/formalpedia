-- Prove2me | Theorems.Thm_lean_workbook_plus_48763
-- name    : lean_workbook_plus_48763
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/e81bf03e-7f55-4fb2-ae1b-bf768d546a73
-- statement:
--   Let $a,b,c>0 .$ Prove that \n $$\frac{3(a^2+b^2+c^2)}{2(ab+bc+ca)} \geq \frac{a}{b+c}+\frac{b}{a+c}+\frac{c}{b+a}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48763 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :  3 * (a ^ 2 + b ^ 2 + c ^ 2) / (2 * (a * b + b * c + c * a)) ≥ a / (b + c) + b / (a + c) + c / (b + a)   :=  by sorry
