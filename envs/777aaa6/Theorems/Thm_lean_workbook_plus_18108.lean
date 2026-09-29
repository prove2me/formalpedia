-- Prove2me | Theorems.Thm_lean_workbook_plus_18108
-- name    : lean_workbook_plus_18108
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/e25765a8-2523-4b6a-8730-1d7a85f0bc5f
-- statement:
--   Just $x^2 + y^2 + z^2 \geq xy + yz + zx$ which is $(x-y)^2 + (y-z)^2 +(z-x)^2 \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18108 : ∀ (x y z: ℝ), x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + z * x   :=  by sorry
