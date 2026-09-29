-- Prove2me | Theorems.Thm_lean_workbook_plus_51302
-- name    : lean_workbook_plus_51302
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/eda94c41-3b4f-49c8-9b89-9dbf9fa6f9f8
-- statement:
--   First equation means $x\in(-1,8)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51302 (x : ℝ) (hx : -1 < x ∧ x < 8) : x ∈ Set.Ioo (-1) 8   :=  by sorry
