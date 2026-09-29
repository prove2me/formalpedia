-- Prove2me | Theorems.Thm_lean_workbook_plus_747
-- name    : lean_workbook_plus_747
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/ebda69ff-99f8-4bb3-ae73-2725e1fa5112
-- statement:
--   Prove that $\frac{a}{a+bc}+\frac{b}{b+ac}+\frac{c}{c+ab}\geq \frac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_747 : ∀ a b c : ℝ, (a / (a + b * c) + b / (b + a * c) + c / (c + a * b) ≥ 3 / 2)   :=  by sorry
