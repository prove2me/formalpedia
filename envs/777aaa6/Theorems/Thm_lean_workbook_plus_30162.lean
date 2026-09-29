-- Prove2me | Theorems.Thm_lean_workbook_plus_30162
-- name    : lean_workbook_plus_30162
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/001679f4-a58e-473f-b4ec-b1b5acc97984
-- statement:
--   Let $a,b$ be positive real numbers. Prove that $\frac{a^4+b^4}{a^3+b^3}\geq\frac{a^2+b^2}{a+b}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30162 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a^4 + b^4) / (a^3 + b^3) ≥ (a^2 + b^2) / (a + b)   :=  by sorry
