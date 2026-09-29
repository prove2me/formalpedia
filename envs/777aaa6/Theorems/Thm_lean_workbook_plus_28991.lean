-- Prove2me | Theorems.Thm_lean_workbook_plus_28991
-- name    : lean_workbook_plus_28991
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/2a4e278b-1a3f-4603-ba7d-90f8ac4c671e
-- statement:
--   $\frac{3}{2}+\frac{ab}{a+b}+\frac{bc}{b+c}+\frac{ca}{c+a}\ge ab+bc+ca \Leftrightarrow \frac{a+b+c}{2}+\sum_{cyc}\frac{ab}{a+b}\geq\frac{3(ab+ac+bc)}{a+b+c} \Leftrightarrow$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28991 : ∀ a b c : ℝ, a + b + c > 0 → 3 / 2 + a * b / (a + b) + b * c / (b + c) + c * a / (c + a) ≥ a * b + b * c + c * a   :=  by sorry
