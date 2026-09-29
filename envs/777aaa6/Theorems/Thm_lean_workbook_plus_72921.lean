-- Prove2me | Theorems.Thm_lean_workbook_plus_72921
-- name    : lean_workbook_plus_72921
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/3eaa0192-cc21-4317-ab4d-0c04bdaf3392
-- statement:
--   For $a, b, c>0, a^2+b^2+c^2=1$ prove that \n $\frac{ab+1}{ab(a^2+ab+b^2)}+\frac{bc+1}{bc(b^2+bc+c^2)}+\frac{ca+1}{ca(c^2+ca+a^2)}\ge 12$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72921 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : (a * b + 1) / (a * b * (a^2 + a * b + b^2)) + (b * c + 1) / (b * c * (b^2 + b * c + c^2)) + (c * a + 1) / (c * a * (c^2 + c * a + a^2)) ≥ 12   :=  by sorry
