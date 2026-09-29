-- Prove2me | Theorems.Thm_lean_workbook_plus_7738
-- name    : lean_workbook_plus_7738
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/dc6ce76e-ef45-4b4f-b5be-5241c4d6eefe
-- statement:
--   Let $a,b,c$ be three positive real numbers , prove that : $\frac{a}{b^2}+\frac{b}{c^2}+\frac{c}{a^2}\ge \frac{1}{a}+ \frac{1}{b}+ \frac{1}{c}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7738 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b ^ 2 + b / c ^ 2 + c / a ^ 2) ≥ (1 / a + 1 / b + 1 / c)   :=  by sorry
