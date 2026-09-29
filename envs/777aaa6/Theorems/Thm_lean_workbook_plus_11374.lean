-- Prove2me | Theorems.Thm_lean_workbook_plus_11374
-- name    : lean_workbook_plus_11374
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/2781408f-6beb-46b5-bb30-9fb59020fe4b
-- statement:
--   Prove the identity: $\cos{x}=1-2\sin^{2}{\frac{x}{2}}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11374 : ∀ x : ℝ, Real.cos x = 1 - 2 * (Real.sin (x / 2))^2   :=  by sorry
