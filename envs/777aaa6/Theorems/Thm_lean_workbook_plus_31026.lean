-- Prove2me | Theorems.Thm_lean_workbook_plus_31026
-- name    : lean_workbook_plus_31026
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/0f02e82d-731d-4c87-bcb8-7f7b6613208d
-- statement:
--   Let $a,b>0.$ Prove that $\frac{a^2}{b}+\frac{b^2}{2a+b}\geq \frac{a+b}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31026 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a^2 / b + b^2 / (2 * a + b) ≥ (a + b) / 2   :=  by sorry
