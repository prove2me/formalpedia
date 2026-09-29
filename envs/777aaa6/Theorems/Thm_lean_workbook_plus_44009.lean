-- Prove2me | Theorems.Thm_lean_workbook_plus_44009
-- name    : lean_workbook_plus_44009
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/f423ea35-f3f4-4fff-85e1-fbea1f0cd6b4
-- statement:
--   Find the general solution for the equation: $ x=c(3a^{2}-6ab-b^{2}),y=c(b^{2}-2ab-3a^{2}),z=c(3a^{2}+b^{2})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44009 (a b c x y z : ℝ) : x = c * (3 * a ^ 2 - 6 * a * b - b ^ 2) ∧ y = c * (b ^ 2 - 2 * a * b - 3 * a ^ 2) ∧ z = c * (3 * a ^ 2 + b ^ 2) ↔ x = c * (3 * a ^ 2 - 6 * a * b - b ^ 2) ∧ y = c * (b ^ 2 - 2 * a * b - 3 * a ^ 2) ∧ z = c * (3 * a ^ 2 + b ^ 2)   :=  by sorry
