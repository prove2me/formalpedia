-- Prove2me | Theorems.Thm_lean_workbook_plus_33371
-- name    : lean_workbook_plus_33371
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/6191b2b8-d713-4287-b4ba-c78776218e13
-- statement:
--   How did we get $|3z^2+12z| <= |3z^2|+|12z|$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33371 : ∀ z : ℂ, ‖3 * z ^ 2 + 12 * z‖ ≤ ‖3 * z ^ 2‖ + ‖12 * z‖   :=  by sorry
