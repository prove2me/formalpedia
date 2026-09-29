-- Prove2me | Theorems.Thm_lean_workbook_plus_9938
-- name    : lean_workbook_plus_9938
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/e5031f6a-a02b-46b0-90d3-fc4ce9e99bbc
-- statement:
--   Prove that $2(a^3+b^3+c^3)+4(ab+bc+ca)+abc \geq 19$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9938 : ∀ a b c : ℝ, 2 * (a ^ 3 + b ^ 3 + c ^ 3) + 4 * (a * b + b * c + c * a) + a * b * c ≥ 19   :=  by sorry
