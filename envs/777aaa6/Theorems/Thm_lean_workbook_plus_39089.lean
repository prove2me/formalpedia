-- Prove2me | Theorems.Thm_lean_workbook_plus_39089
-- name    : lean_workbook_plus_39089
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/2c098af8-d1d8-4658-925a-b7a0a6392c88
-- statement:
--   For $a,b,c>0$ . Prove that $\frac{9}{4}\cdot \sum_{cyc} a(a+b)(c+a)\geqq (a+b+c)^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39089 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (9 / 4) * (a * (a + b) * (a + c) + b * (b + c) * (b + a) + c * (c + a) * (c + b)) ≥ (a + b + c) ^ 3   :=  by sorry
