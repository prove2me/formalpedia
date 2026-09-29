-- Prove2me | Theorems.Thm_lean_workbook_plus_21372
-- name    : lean_workbook_plus_21372
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/359a9297-1102-4bf0-abcc-79501314c20c
-- statement:
--   Prove the identity: $\cos{x}+\cos{y}=2\cos{\frac{x+y}{2}}\cos{\frac{x-y}{2}}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21372 : ∀ x y : ℝ, cos x + cos y = 2 * cos ((x + y) / 2) * cos ((x - y) / 2)   :=  by sorry
