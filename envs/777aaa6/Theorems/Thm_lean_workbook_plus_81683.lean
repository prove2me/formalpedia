-- Prove2me | Theorems.Thm_lean_workbook_plus_81683
-- name    : lean_workbook_plus_81683
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/b4da5ac1-984d-4e8a-ac79-bfb7c2795811
-- statement:
--   Prove that $2(a^2+b^2+c^2)^2\geq 27-3(a^2b+b^2c+c^2a)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81683 : ∀ a b c : ℝ, 2 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 27 - 3 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a)   :=  by sorry
