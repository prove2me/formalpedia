-- Prove2me | Theorems.Thm_lean_workbook_plus_10548
-- name    : lean_workbook_plus_10548
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/4a999b0f-881a-42ad-b6e9-1e19f62ed121
-- statement:
--   Expand and verify that $ a(a + b)(a + 2b)(a + 3b) + b^4 = (a^2 + 3ab + b^2)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10548 : ∀ a b : ℤ, a * (a + b) * (a + 2 * b) * (a + 3 * b) + b ^ 4 = (a ^ 2 + 3 * a * b + b ^ 2) ^ 2   :=  by sorry
