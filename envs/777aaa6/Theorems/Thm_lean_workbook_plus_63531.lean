-- Prove2me | Theorems.Thm_lean_workbook_plus_63531
-- name    : lean_workbook_plus_63531
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/eb52940e-90ac-4f3d-a425-c6f9fb711e73
-- statement:
--   For $a,b>0,\frac{1}{a}+\frac{1}{b}=1.$ Prove that $\frac{ a^2}{a+2b }+\frac{ b^2 }{b+2a} \geq \frac{4}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63531 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 1 / a + 1 / b = 1) : a^2 / (a + 2 * b) + b^2 / (b + 2 * a) ≥ 4 / 3   :=  by sorry
