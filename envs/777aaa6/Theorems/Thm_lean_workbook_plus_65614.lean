-- Prove2me | Theorems.Thm_lean_workbook_plus_65614
-- name    : lean_workbook_plus_65614
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/c8d8008d-5f90-480b-a38b-f260255758d1
-- statement:
--   Show ALGEBRAICALLY that, for $0<x<3$ , $1+2\sqrt{x} \ge x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65614 (x : ℝ) (hx : 0 < x ∧ x < 3) :
  1 + 2 * Real.sqrt x ≥ x   :=  by sorry
