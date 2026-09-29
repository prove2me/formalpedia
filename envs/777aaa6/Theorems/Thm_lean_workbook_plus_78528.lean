-- Prove2me | Theorems.Thm_lean_workbook_plus_78528
-- name    : lean_workbook_plus_78528
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/8d1c6477-d3f1-45a5-8dfc-bff9ea2eae4b
-- statement:
--   For all real $ x,y,z$ prove that $ 5(x^2+y^2+z^2)\geq 6xy-8xz+8yz $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78528 : ∀ x y z : ℝ, 5 * (x ^ 2 + y ^ 2 + z ^ 2) ≥ 6 * x * y - 8 * x * z + 8 * y * z   :=  by sorry
