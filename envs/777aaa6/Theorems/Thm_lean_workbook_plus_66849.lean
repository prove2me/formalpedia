-- Prove2me | Theorems.Thm_lean_workbook_plus_66849
-- name    : lean_workbook_plus_66849
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/48d73a79-552f-47cf-b7ca-d7273e149130
-- statement:
--   For what real values of $x$ is $\sqrt{(144-x^{2})^{2}}=144-x^{2}$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66849 : ∀ x : ℝ, (Real.sqrt ((144 - x ^ 2) ^ 2) = 144 - x ^ 2) ↔ (0 ≤ 144 - x ^ 2)   :=  by sorry
