-- Prove2me | Theorems.Thm_lean_workbook_plus_36605
-- name    : lean_workbook_plus_36605
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/20b0944b-86a3-4db2-a7ef-c029bb924c6e
-- statement:
--   Prove, that for all reals $b, c$ , we have $b^2c^2+b^2+1\geq b+b^2c+bc.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36605 : ∀ b c : ℝ, b^2 * c^2 + b^2 + 1 ≥ b + b^2 * c + b * c   :=  by sorry
