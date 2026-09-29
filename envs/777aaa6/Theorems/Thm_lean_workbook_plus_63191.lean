-- Prove2me | Theorems.Thm_lean_workbook_plus_63191
-- name    : lean_workbook_plus_63191
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/d2f8ac84-8d4c-49c0-bc40-f0d6c41c49b7
-- statement:
--   Prove that $ \frac{ sin^2 a}{1+cos a} + \frac{sin^2 a}{1-cos a }= 2 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63191 : ∀ a : ℝ, ( sin a ^ 2 / (1 + cos a) + sin a ^ 2 / (1 - cos a) ) = 2   :=  by sorry
