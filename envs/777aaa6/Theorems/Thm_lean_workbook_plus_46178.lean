-- Prove2me | Theorems.Thm_lean_workbook_plus_46178
-- name    : lean_workbook_plus_46178
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/ef7329dc-bd53-4e43-9b05-46b3ed15d761
-- statement:
--   Let triangle ABC, prove that: $\sum_{cyc}^{A,B,C}(sin\frac{A}{2})^2\geq 4\sum_{cyc}^{A,B,C}(sin\frac{B}{2})^2(sin\frac{C}{2})^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46178 (A B C : ℝ) (hx: A > 0 ∧ B > 0 ∧ C > 0) (hab : A + B + C = π) : (sin A / 2)^2 + (sin B / 2)^2 + (sin C / 2)^2 ≥ 4 * ((sin A / 2)^2 * (sin B / 2)^2 + (sin B / 2)^2 * (sin C / 2)^2 + (sin C / 2)^2 * (sin A / 2)^2)   :=  by sorry
