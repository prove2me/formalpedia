-- Prove2me | Theorems.Thm_lean_workbook_plus_77944
-- name    : lean_workbook_plus_77944
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/39b21a2a-a3f6-4c64-b89b-eeacd322c3f2
-- statement:
--   prove that: $ (xy)^2 + (yz)^2 + (zx)^2 >\frac {x^4 + y^4 + z^4}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77944 : ∀ x y z : ℝ, (x * y) ^ 2 + (y * z) ^ 2 + (z * x) ^ 2 > (x ^ 4 + y ^ 4 + z ^ 4) / 2   :=  by sorry
