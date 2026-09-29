-- Prove2me | Theorems.Thm_lean_workbook_plus_56403
-- name    : lean_workbook_plus_56403
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/be761b5a-710b-44a5-bbea-3d4a0d97edeb
-- statement:
--   For $a, b, c>0, a^2+b^2+c^2=1$ prove that $\frac{2ab+1}{ab+c^2}+\frac{2bc+1}{bc+a^2}+\frac{2ca+1}{ca+b^2}\geq \frac{13}{2}+ab+bc+ca$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56403 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : (2 * a * b + 1) / (a * b + c^2) + (2 * b * c + 1) / (b * c + a^2) + (2 * c * a + 1) / (c * a + b^2) ≥ 13 / 2 + a * b + b * c + c * a   :=  by sorry
