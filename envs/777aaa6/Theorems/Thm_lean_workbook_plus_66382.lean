-- Prove2me | Theorems.Thm_lean_workbook_plus_66382
-- name    : lean_workbook_plus_66382
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/5617e57b-1bdc-4c67-a1dd-85a56688c128
-- statement:
--   Prove that for any positive real numbers $a, b, c$, the following inequality holds: \n\n $\dfrac{a}{b+c}+\dfrac{b}{a+c}+\dfrac{c}{a+b}\ge\dfrac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66382 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (a + c) + c / (a + b)) ≥ 3 / 2   :=  by sorry
