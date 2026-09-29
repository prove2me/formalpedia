-- Prove2me | Theorems.Thm_lean_workbook_plus_1002
-- name    : lean_workbook_plus_1002
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/526d7311-c12c-4b64-b1c3-f541f6b86e33
-- statement:
--   Given two fractions $\frac{a}{b}$ and $\frac{c}{d}$ where $a,b,c,d > 0$ and $\frac{a}{b} < \frac{c}{d}$, prove that $\frac{a}{b} < \frac{a+c}{b+d} < \frac{c}{d}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1002 (a b c d : ℝ) (hb : 0 < b) (hd : 0 < d) (h : a / b < c / d) : a / b < (a + c) / (b + d) ∧ (a + c) / (b + d) < c / d   :=  by sorry
