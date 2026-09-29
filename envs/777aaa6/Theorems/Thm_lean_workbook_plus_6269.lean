-- Prove2me | Theorems.Thm_lean_workbook_plus_6269
-- name    : lean_workbook_plus_6269
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/2d06d564-ae8d-4691-8886-cf42d6868f9b
-- statement:
--   Prove that $ 2bc+2b^2+2c^2 \leq 6+b^3c+bc^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6269 : ∀ b c : ℝ, 2 * b * c + 2 * b^2 + 2 * c^2 ≤ 6 + b^3 * c + b * c^3   :=  by sorry
