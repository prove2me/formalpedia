-- Prove2me | Theorems.Thm_lean_workbook_plus_47728
-- name    : lean_workbook_plus_47728
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/153fc9c5-f9fc-40f6-8ea2-f103b7d4b657
-- statement:
--   Prove that $\sqrt{2(a^2+b^2)} \ge a+b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47728 : ∀ a b : ℝ, Real.sqrt (2 * (a ^ 2 + b ^ 2)) ≥ a + b   :=  by sorry
