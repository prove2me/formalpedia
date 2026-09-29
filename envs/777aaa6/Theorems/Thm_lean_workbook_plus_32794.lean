-- Prove2me | Theorems.Thm_lean_workbook_plus_32794
-- name    : lean_workbook_plus_32794
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/b0bae9ee-1f02-4900-9061-9af219ca3616
-- statement:
--   If $a,b,c$ are positive real numbers, and $a^{2}+b^{2}+c^{2}=1$ , prove: $\frac{a}{b^{2}+1}+\frac{b}{c^{2}+1}+\frac{c}{a^{2}+1}\geq \frac{3}{4}(a \sqrt a+b \sqrt b+c \sqrt c)^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32794 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (hab : a + b + c = 1) : a / (b * b + 1) + b / (c * c + 1) + c / (a * a + 1) ≥ (3 / 4) * (a * Real.sqrt a + b * Real.sqrt b + c * Real.sqrt c) ^ 2   :=  by sorry
