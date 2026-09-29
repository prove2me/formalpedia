-- Prove2me | Theorems.Thm_lean_workbook_plus_60642
-- name    : lean_workbook_plus_60642
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/5bb13f2e-73ed-450e-9604-da66a14368e7
-- statement:
--   Let $a,b>0 .$ Prove that \n $$\frac{a}{b} + \frac{b}{a} + \frac{kab}{a^2 +b^2} \geq \frac{k+4}{2}$$ Where $0\leq k\leq 4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60642 (a b : ℝ) (hab : 0 < a ∧ 0 < b) (k : ℝ) (hk : 0 ≤ k ∧ k ≤ 4) : a / b + b / a + k * a * b / (a ^ 2 + b ^ 2) ≥ (k + 4) / 2   :=  by sorry
