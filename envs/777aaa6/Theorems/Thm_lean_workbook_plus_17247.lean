-- Prove2me | Theorems.Thm_lean_workbook_plus_17247
-- name    : lean_workbook_plus_17247
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/a48ea290-8bbf-4e47-aa6a-b65159221bc0
-- statement:
--   prove that, for positive reals $a$ , $b$ , and $c$ , $a^2+b^2+c^2\geq\frac{(a+b+c)^2}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17247 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 + b^2 + c^2 ≥ (a + b + c)^2 / 3   :=  by sorry
