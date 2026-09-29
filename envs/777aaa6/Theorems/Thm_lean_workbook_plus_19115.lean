-- Prove2me | Theorems.Thm_lean_workbook_plus_19115
-- name    : lean_workbook_plus_19115
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/9f31b659-f464-45a6-8b95-f01aa16e45b0
-- statement:
--   In $\triangle ABC $ ,Prove that \n $sin\frac {A}{3}sin\frac {B}{3}sin\frac {C}{3}\le sin\frac {\pi-A}{6}sin\frac {\pi-B}{6}sin\frac {\pi-C}{6}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19115 : ∀ A B C : ℝ, A > 0 ∧ B > 0 ∧ C > 0 ∧ A + B + C = π → sin A / 3 * sin B / 3 * sin C / 3 ≤ sin (π - A) / 6 * sin (π - B) / 6 * sin (π - C) / 6   :=  by sorry
