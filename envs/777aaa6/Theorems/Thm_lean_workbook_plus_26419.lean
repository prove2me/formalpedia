-- Prove2me | Theorems.Thm_lean_workbook_plus_26419
-- name    : lean_workbook_plus_26419
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/49d7f9b6-e530-41c0-8da9-abfcfa6987ac
-- statement:
--   Factor $x^7 + 1$ using roots of unity and comment on the closed form of the quadratic factors.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26419 : ∀ x : ℂ, x^7 + 1 = (x + 1) * (x^6 - x^5 + x^4 - x^3 + x^2 - x + 1)   :=  by sorry
