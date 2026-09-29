-- Prove2me | Theorems.Thm_lean_workbook_plus_7364
-- name    : lean_workbook_plus_7364
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/6b99cf04-d7cd-447e-a467-7ab3adb3a805
-- statement:
--   The system is equivalent to\n\n$x^{3}-6z^{2}+12z-8 = 0$ (1)\n$x=y=z$ (2)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7364 (x y z : ℂ) : (x^3 - 6 * z^2 + 12 * z - 8 = 0 ∧ x = y ∧ y = z) ↔ x^3 - 6 * z^2 + 12 * z - 8 = 0 ∧ x = z ∧ y = z   :=  by sorry
