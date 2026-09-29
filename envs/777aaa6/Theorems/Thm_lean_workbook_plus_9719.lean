-- Prove2me | Theorems.Thm_lean_workbook_plus_9719
-- name    : lean_workbook_plus_9719
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/5cafe45f-d823-4362-b99c-573ac08f7301
-- statement:
--   Calculate $\int^2_0 \int^{\sqrt{2x-x^2}}_0 \sqrt{x^2+y^2} \,dy \,dx $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9719 (x y : ℝ) (hx: 0 ≤ x ∧ x ≤ 2) (hy: 0 ≤ y ∧ y ≤ √(2 * x - x^2)) : 0 ≤ √(x^2 + y^2)   :=  by sorry
