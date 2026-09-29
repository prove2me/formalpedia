-- Prove2me | Theorems.Thm_lean_workbook_plus_7389
-- name    : lean_workbook_plus_7389
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/05196b6a-ac79-4254-a725-5c37d0094ba4
-- statement:
--   Find the number of real solutions to $4x^2 - 40 \lfloor x \rfloor + 51 = 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7389 (f : ℝ → ℝ) : (∃ x, 4*x^2 - 40 * Int.floor x + 51 = 0) ↔ ∃ x, 4*x^2 - 40 * Int.ceil x + 51 = 0   :=  by sorry
