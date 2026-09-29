-- Prove2me | Theorems.Thm_lean_workbook_plus_36233
-- name    : lean_workbook_plus_36233
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/cec0b76b-779c-459f-a431-a53e21e0b897
-- statement:
--   Prove the inequality\n$a^4+b^4+c^4+abc(a+b+c)\\leq2(a^2b^2+b^2c^2+c^2a^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36233 : ∀ a b c : ℝ, a^4 + b^4 + c^4 + a * b * c * (a + b + c) ≤ 2 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)   :=  by sorry
