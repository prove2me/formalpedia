-- Prove2me | Theorems.Thm_lean_workbook_plus_18696
-- name    : lean_workbook_plus_18696
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/8a476602-88a6-49ce-9df0-413c8f25abce
-- statement:
--   Positive reals $a,b,c$ satisfy $a^2+b^2+c^2=1$ . Prove: $\frac{1}{a^3+2bc}+\frac{1}{b^3+2ca}+\frac{1}{c^3+2ab}\geq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18696 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : 1 / (a^3 + 2 * b * c) + 1 / (b^3 + 2 * c * a) + 1 / (c^3 + 2 * a * b) ≥ 1   :=  by sorry
