-- Prove2me | Theorems.Thm_lean_workbook_plus_21514
-- name    : lean_workbook_plus_21514
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/7a0142d0-535a-45fa-aab0-5db4901e4803
-- statement:
--   Verify the equality \(\frac{1}{a + bi} = \frac{a - bi}{a^2 + b^2}\) without calculation.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21514 : ∀ a b : ℝ, (a - b * Complex.I) / (a ^ 2 + b ^ 2) = (a + b * Complex.I)⁻¹   :=  by sorry
