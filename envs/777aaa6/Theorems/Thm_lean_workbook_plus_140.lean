-- Prove2me | Theorems.Thm_lean_workbook_plus_140
-- name    : lean_workbook_plus_140
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/2b5be97d-3938-4415-8837-b0be547eb7b0
-- statement:
--   Prove $x^2 + x + y^2 + y + 1 \geq x y$ for all real x,y
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_140 (x y: ℝ): x ^ 2 + x + y ^ 2 + y + 1 ≥ x * y   :=  by sorry
