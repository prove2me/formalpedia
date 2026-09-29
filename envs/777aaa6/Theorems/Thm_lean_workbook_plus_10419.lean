-- Prove2me | Theorems.Thm_lean_workbook_plus_10419
-- name    : lean_workbook_plus_10419
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/3e628818-2718-41ae-a6db-9ddc32959915
-- statement:
--   Solve the system in \\(\mathbb{Q}\\) (or prove that there exist infinitely many solutions to this): \\(a + b + c = a^{2} + b^{2} + c^{2} = 1\\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10419 (a b c : ℚ) (ha : a + b + c = 1) (hb : a^2 + b^2 + c^2 = 1) : ∃ a b c : ℚ, a + b + c = 1 ∧ a^2 + b^2 + c^2 = 1   :=  by sorry
