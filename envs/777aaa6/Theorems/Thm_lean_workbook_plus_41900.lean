-- Prove2me | Theorems.Thm_lean_workbook_plus_41900
-- name    : lean_workbook_plus_41900
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/9e7375a6-d5d9-400a-8b2c-2fe5f1540067
-- statement:
--   Factorize $x^4+4x^2+16$ over real numbers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41900 : ∀ x : ℝ, x^4 + 4 * x^2 + 16 = (x^2 + 2 * x + 4) * (x^2 - 2 * x + 4)   :=  by sorry
