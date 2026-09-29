-- Prove2me | Theorems.Thm_lean_workbook_plus_7175
-- name    : lean_workbook_plus_7175
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/517a9b9d-8308-4fad-98f6-5cac20a95209
-- statement:
--   $ z=\frac{2a+b+4c}{7}$ , $ x=\frac{4a+2b+c}{7}$ , $ y=\frac{a+4b+2c}{7}$ ----->
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7175 (a b c x y z : ℝ) : x = (4 * a + 2 * b + c) / 7 ∧ y = (a + 4 * b + 2 * c) / 7 ∧ z = (2 * a + b + 4 * c) / 7 ↔ x = (4 * a + 2 * b + c) / 7 ∧ y = (a + 4 * b + 2 * c) / 7 ∧ z = (2 * a + b + 4 * c) / 7   :=  by sorry
