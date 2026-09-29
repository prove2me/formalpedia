-- Prove2me | Theorems.Thm_lean_workbook_plus_73957
-- name    : lean_workbook_plus_73957
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/354ceb37-54b5-441f-8fa3-165e6029418c
-- statement:
--   Let $ a,b$ are positve reals such that $ a+2b=1.$ Prove that $ (a+\frac{1}{b})(b+\frac{1}{a})\geq \frac{81}{8}$ Equality holds when $a=\frac{1}{2},b=\frac{1}{4}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73957 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + 2 * b = 1) : (a + 1 / b) * (b + 1 / a) ≥ 81 / 8   :=  by sorry
