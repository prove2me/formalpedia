-- Prove2me | Theorems.Thm_lean_workbook_plus_68244
-- name    : lean_workbook_plus_68244
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/98e3fd55-f2c1-476f-b4ee-8acecf960f45
-- statement:
--   Then $ a+b+c+\frac{1}{a}+\frac{1}{b}+\frac{1}{c} \geq a+b+c+\frac{9}{a+b+c}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68244 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : a + b + c + 1 / a + 1 / b + 1 / c ≥ a + b + c + 9 / (a + b + c)   :=  by sorry
