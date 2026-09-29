-- Prove2me | Theorems.Thm_lean_workbook_plus_81139
-- name    : lean_workbook_plus_81139
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/d1f8596f-bc42-437f-a245-e771422a4d84
-- statement:
--   Prove that\n\n$$\frac{a^2+b^2+c^2+ab+bc+ca+1}{a^2+b^2+c^2}+\frac{2}{ab+bc+ca} \leq \frac{a(b+c+1)}{a^2+2bc}+\frac{b(c+a+1)}{b^2+2ca}+\frac{c(a+b+1)}{c^2+2ab} \leq \frac{a(a+b+1)+b(b+c+1)+c(c+a+1)}{ab+bc+ca}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81139 : ∀ a b c : ℝ, (a^2 + b^2 + c^2 + a * b + b * c + c * a + 1) / (a^2 + b^2 + c^2) + 2 / (a * b + b * c + c * a) ≤ a * (b + c + 1) / (a^2 + 2 * b * c) + b * (c + a + 1) / (b^2 + 2 * c * a) + c * (a + b + 1) / (c^2 + 2 * a * b) ∧ a * (b + c + 1) / (a^2 + 2 * b * c) + b * (c + a + 1) / (b^2 + 2 * c * a) + c * (a + b + 1) / (c^2 + 2 * a * b) ≤ (a * (a + b + 1) + b * (b + c + 1) + c * (c + a + 1)) / (a * b + b * c + c * a)   :=  by sorry
