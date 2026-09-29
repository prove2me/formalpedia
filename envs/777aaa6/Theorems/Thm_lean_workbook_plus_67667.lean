-- Prove2me | Theorems.Thm_lean_workbook_plus_67667
-- name    : lean_workbook_plus_67667
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/96c6d8b5-92b2-4798-8ad5-53e6bf68db28
-- statement:
--   $0<x<1 \implies 0 < x^2< 1 \implies 0<56x^2<56$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67667 : ∀ x : ℝ, 0 < x ∧ x < 1 → 0 < 56 * x^2 ∧ 56 * x^2 < 56   :=  by sorry
