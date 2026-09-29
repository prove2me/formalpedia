-- Prove2me | Theorems.Thm_lean_workbook_plus_46141
-- name    : lean_workbook_plus_46141
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/4aaf5b70-7b11-4347-9177-b56d4aa78966
-- statement:
--   Prove that $ cosA + cosB + cosC\geq \frac {1}{4}(3 + cos(A - B) + cos(B - C) + cos(C - A))$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46141 : ∀ A B C : ℝ, cos A + cos B + cos C ≥ 1 / 4 * (3 + cos (A - B) + cos (B - C) + cos (C - A))   :=  by sorry
