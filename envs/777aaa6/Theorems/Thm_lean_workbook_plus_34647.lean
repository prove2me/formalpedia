-- Prove2me | Theorems.Thm_lean_workbook_plus_34647
-- name    : lean_workbook_plus_34647
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/53bd40b0-bd1d-4287-a461-ecfb2c95c270
-- statement:
--   $4x-17y=1\implies 4x=1+17y\implies x=\frac{1+17y}{4}……(2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34647 (x y : ℝ) (h₁ : 4*x - 17*y = 1) : x = (1 + 17*y)/4   :=  by sorry
