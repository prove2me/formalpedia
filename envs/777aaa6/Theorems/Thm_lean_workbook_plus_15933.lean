-- Prove2me | Theorems.Thm_lean_workbook_plus_15933
-- name    : lean_workbook_plus_15933
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/625d699e-4ff9-4a9b-ad9e-e203980df934
-- statement:
--   Let a,b,c>0. Prove that: $$ \frac{b^2+c^2}{b+c}+\frac{a^2+b^2}{a+b}+\frac{c^2+a^2}{c+ a}\geq\frac{2(a^2+b^2+c^2)+ab+bc+ca}{a+b+c}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15933 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b^2 + c^2) / (b + c) + (a^2 + b^2) / (a + b) + (c^2 + a^2) / (c + a) ≥ (2 * (a^2 + b^2 + c^2) + a * b + b * c + c * a) / (a + b + c)   :=  by sorry
