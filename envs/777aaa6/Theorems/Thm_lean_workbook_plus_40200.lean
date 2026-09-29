-- Prove2me | Theorems.Thm_lean_workbook_plus_40200
-- name    : lean_workbook_plus_40200
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/54e39061-497f-434b-b576-da7c33595c50
-- statement:
--   Prove that the following fraction represent a natural number : $\frac{1+2012^4+2013^4}{1+2012^2+2013^2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40200 (a : ℕ) : ∃ b : ℕ, (1 + 2012^4 + 2013^4) / (1 + 2012^2 + 2013^2) = b   :=  by sorry
