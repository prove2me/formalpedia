-- Prove2me | Theorems.Thm_lean_workbook_plus_19547
-- name    : lean_workbook_plus_19547
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/7d414f45-65bc-4869-8e0b-87275b8bc0c7
-- statement:
--   For positives $a$ , $b$ and $c$ such that $a^2+b^2+c^2=1$ prove that: $17(a+b+c)+\frac{1}{abc}\geq20\sqrt3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19547 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : 17 * (a + b + c) + 1 / (a * b * c) ≥ 20 * Real.sqrt 3   :=  by sorry
