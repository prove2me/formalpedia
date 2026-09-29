-- Prove2me | Theorems.Thm_lean_workbook_plus_41922
-- name    : lean_workbook_plus_41922
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/1d232657-78c6-4098-8bbb-18805f970767
-- statement:
--   Prove that $cos^3{x}-cos^2{x}=cos^2{x}(cos{x}-1)\le 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41922 : ∀ x : ℝ, (cos x)^3 - (cos x)^2 = (cos x)^2 * (cos x - 1) ∧ (cos x)^2 * (cos x - 1) ≤ 0   :=  by sorry
