-- Prove2me | Theorems.Thm_lean_workbook_plus_60372
-- name    : lean_workbook_plus_60372
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/cd16c49c-67d3-4a78-a879-e752e3900f01
-- statement:
--   Prove that $2\sin x\cos y=\sin (x+y)+\sin(x-y)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60372 : ∀ x y : ℝ, 2 * sin x * cos y = sin (x + y) + sin (x - y)   :=  by sorry
