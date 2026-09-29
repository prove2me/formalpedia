-- Prove2me | Theorems.Thm_lean_workbook_plus_38996
-- name    : lean_workbook_plus_38996
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/b450881e-db94-489f-b3d7-4dee73812147
-- statement:
--   Prove that $\sin\theta = \cos(90 - \theta)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38996 : ∀ θ, sin θ = cos (π / 2 - θ)   :=  by sorry
