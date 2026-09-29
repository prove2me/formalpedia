-- Prove2me | Theorems.Thm_lean_workbook_plus_49021
-- name    : lean_workbook_plus_49021
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/256d0e6b-3242-4101-968d-ea7887d7c5bf
-- statement:
--   Prove that $3abc \leq a^3 + b^3 + c^3$ using AM-GM inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49021 : ∀ a b c : ℝ, 3 * a * b * c ≤ a ^ 3 + b ^ 3 + c ^ 3   :=  by sorry
