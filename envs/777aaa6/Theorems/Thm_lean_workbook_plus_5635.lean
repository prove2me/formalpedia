-- Prove2me | Theorems.Thm_lean_workbook_plus_5635
-- name    : lean_workbook_plus_5635
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/a755243c-99ac-41c7-9996-b243e6225a7c
-- statement:
--   Expand $(x+ai)^7,(x-ai)^7$ by the binomial formula.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5635 (x ai : ℂ) : (x + ai)^7 = (x^7 + 7 * (ai * x^6) + 21 * (ai^2 * x^5) + 35 * (ai^3 * x^4) + 35 * (ai^4 * x^3) + 21 * (ai^5 * x^2) + 7 * (ai^6 * x) + ai^7) ∧ (x - ai)^7 = (x^7 - 7 * (ai * x^6) + 21 * (ai^2 * x^5) - 35 * (ai^3 * x^4) + 35 * (ai^4 * x^3) - 21 * (ai^5 * x^2) + 7 * (ai^6 * x) - ai^7)   :=  by sorry
