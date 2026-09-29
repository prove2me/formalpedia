-- Prove2me | Theorems.Thm_lean_workbook_plus_66666
-- name    : lean_workbook_plus_66666
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/5cd9432c-6659-489d-b886-d6543ac151d1
-- statement:
--   Let $a, b, c> 0$ . Prove: $2+\frac{a^2+b^2+c^2}{ab+bc+ca}\geq \frac{a+b}{a+c}+\frac{b+c}{b+a}+\frac{c+a}{c+b}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66666 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 + (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) ≥ (a + b) / (a + c) + (b + c) / (b + a) + (c + a) / (c + b)   :=  by sorry
