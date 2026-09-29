-- Prove2me | Theorems.Thm_lean_workbook_plus_53311
-- name    : lean_workbook_plus_53311
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/8e82a77b-1234-4196-8545-06162b04804c
-- statement:
--   Prove that for positive real numbers a, b, and c, the following inequality holds: \n$ \frac{a^{2}}{b}+\frac{b^{2}}{c}+\frac{c^{2}}{a}\ge\frac{(a+b+c)(a^{2}+b^{2}+c^{2})}{ab+bc+ca}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53311 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / b + b^2 / c + c^2 / a) ≥ (a + b + c) * (a^2 + b^2 + c^2) / (a * b + b * c + a * c)   :=  by sorry
