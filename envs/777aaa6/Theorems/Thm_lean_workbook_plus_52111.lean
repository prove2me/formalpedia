-- Prove2me | Theorems.Thm_lean_workbook_plus_52111
-- name    : lean_workbook_plus_52111
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/f0d5e3a5-65aa-4e64-aa1f-74b6e6304498
-- statement:
--   Prove that the polynomial $f(a,b,c) = (a^2+ab+b^2)(\frac{3}{4}c^2+(a+\frac{c}{2})^2)(\frac{3}{4}c^2+(b+\frac{c}{2})^2)$ increases when $\frac{3a+3b}{a^2+ab+b^2}\geq\frac{3c}{a^2+ac+c^2}+\frac{3c}{b^2+bc+c^2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52111 (a b c : ℝ) : (3 * a + 3 * b) / (a ^ 2 + a * b + b ^ 2) ≥ (3 * c) / (a ^ 2 + a * c + c ^ 2) + (3 * c) / (b ^ 2 + b * c + c ^ 2) → (a ^ 2 + a * b + b ^ 2) * (3 / 4 * c ^ 2 + (a + c / 2) ^ 2) * (3 / 4 * c ^ 2 + (b + c / 2) ^ 2) ≥ (a ^ 2 + b ^ 2 + a * b) * (3 / 4 * c ^ 2 + (a + c / 2) ^ 2) * (3 / 4 * c ^ 2 + (b + c / 2) ^ 2)   :=  by sorry
