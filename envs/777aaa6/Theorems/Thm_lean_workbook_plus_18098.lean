-- Prove2me | Theorems.Thm_lean_workbook_plus_18098
-- name    : lean_workbook_plus_18098
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/22e3a4fa-04c3-4628-8877-905dadf7c8c7
-- statement:
--   It equal to\n$2\sin \frac{A}{2}\ge \cos B+\cos C\Longleftrightarrow 2\sin \frac{A}{2}\ge 2\cos \frac{B+C}{2}\cos \frac{B-C}{2}$\nWhich means $\cos \frac{B-C}{2}\le 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18098 ∀ A B C : ℝ, A > 0 ∧ B > 0 ∧ C > 0 → A + B + C = π → 2 * Real.sin (A / 2) ≥ Real.cos B + Real.cos C ↔  2 * Real.sin (A / 2) ≥ 2 * Real.cos ((B + C) / 2) * Real.cos ((B - C) / 2)   :=  by sorry
