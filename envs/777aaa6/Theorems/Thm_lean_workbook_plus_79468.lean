-- Prove2me | Theorems.Thm_lean_workbook_plus_79468
-- name    : lean_workbook_plus_79468
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/843e1a23-b306-49d6-99a6-3840f3317f3b
-- statement:
--   $2\sin{\frac{B}{2}}\geq \cos A+\cos B+\cos C-1+\cos{A}\cos{C}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79468 : ∀ A B C : ℝ, 2*sin (B/2) ≥ cos A + cos B + cos C - 1 + cos A * cos C   :=  by sorry
