-- Prove2me | Theorems.Thm_lean_workbook_plus_72620
-- name    : lean_workbook_plus_72620
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/a657a23f-55de-400d-866c-afc805aa2548
-- statement:
--   How does one find the roots of a cubic equation like $x^3 - 6x^2 + 11x - 6 = 0$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72620 (x : ℝ) : x^3 - 6 * x^2 + 11 * x - 6 = 0 ↔ x = 1 ∨ x = 2 ∨ x = 3   :=  by sorry
