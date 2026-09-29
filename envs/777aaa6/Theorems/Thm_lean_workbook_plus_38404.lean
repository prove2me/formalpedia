-- Prove2me | Theorems.Thm_lean_workbook_plus_38404
-- name    : lean_workbook_plus_38404
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/5db9750b-bbeb-46b0-9de3-81ff8d045908
-- statement:
--   Prove that $(a + b + c)^2 \geq 3(ab + bc + ca)$ using the identity $(a + b + c)^2 = a^2 + b^2 + c^2 + 2(ab + bc + ca)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38404 : ∀ a b c : ℝ, (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a)   :=  by sorry
