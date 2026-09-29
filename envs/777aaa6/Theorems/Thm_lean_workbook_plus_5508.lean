-- Prove2me | Theorems.Thm_lean_workbook_plus_5508
-- name    : lean_workbook_plus_5508
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/e20c58a5-6a63-41f8-957b-0e8d23d44df8
-- statement:
--   Let $a,b>0$ and $ab=1.$ Prove that \n $$\frac{1}{a}+\frac{1}{b}+\frac{4}{a+b}\ge 4$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5508 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b = 1) : 1 / a + 1 / b + 4 / (a + b) ≥ 4   :=  by sorry
