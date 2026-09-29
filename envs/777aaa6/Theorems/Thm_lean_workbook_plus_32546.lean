-- Prove2me | Theorems.Thm_lean_workbook_plus_32546
-- name    : lean_workbook_plus_32546
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/a96f18f1-c2ca-4d92-97fb-5f33e05462b0
-- statement:
--   $ s^2 - c^2 = \sin^2{\theta} - \cos^2{\theta} = - \cos{2\theta}$ (double angle formula for cosine)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32546 :
  ∀ s c θ : ℝ, s^2 - c^2 = - Real.cos (2 * θ)   :=  by sorry
