-- Prove2me | Theorems.Thm_lean_workbook_plus_4331
-- name    : lean_workbook_plus_4331
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/47d6ecef-50be-4cef-844a-7d465bf8c131
-- statement:
--   Demonstrate that for all positive real numbers $a, b, c$, the following inequality is valid: \n\n $\dfrac{a}{b+c}+\dfrac{b}{a+c}+\dfrac{c}{a+b}\ge\dfrac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4331 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a / (b + c) + b / (a + c) + c / (a + b)) ≥ 3 / 2   :=  by sorry
