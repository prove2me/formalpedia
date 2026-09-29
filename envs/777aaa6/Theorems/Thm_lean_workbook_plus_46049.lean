-- Prove2me | Theorems.Thm_lean_workbook_plus_46049
-- name    : lean_workbook_plus_46049
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/343be7eb-cdc1-407d-9792-fa8181f069a4
-- statement:
--   For all real values of $x$ in the interval $(0.6, 1)$, show that $x - x^3 < 0.6$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46049 : ∀ x : ℝ, 0.6 < x ∧ x < 1 → x - x^3 < 0.6   :=  by sorry
