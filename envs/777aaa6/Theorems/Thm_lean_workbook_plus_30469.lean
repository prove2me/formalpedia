-- Prove2me | Theorems.Thm_lean_workbook_plus_30469
-- name    : lean_workbook_plus_30469
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/e847c864-d443-4713-9b4a-fd3fc226bdc1
-- statement:
--   Prove that $ 2-a-bc \geq -a(b-1)(c-1) $.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30469 : ∀ a b c : ℝ, 2 - a - b * c ≥ -a * (b - 1) * (c - 1)   :=  by sorry
