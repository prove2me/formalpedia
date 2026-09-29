-- Prove2me | Theorems.Thm_lean_workbook_plus_81773
-- name    : lean_workbook_plus_81773
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/3fb37dc3-dee7-4dd6-8f65-9f157a33b9a0
-- statement:
--   Prove that $x^2+xy+y^2-x-y+1 \geq \frac{2}{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81773 : ∀ x y : ℝ, x^2 + x*y + y^2 - x - y + 1 ≥ 2/3   :=  by sorry
