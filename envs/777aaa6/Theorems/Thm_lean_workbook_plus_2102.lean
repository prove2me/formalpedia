-- Prove2me | Theorems.Thm_lean_workbook_plus_2102
-- name    : lean_workbook_plus_2102
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/5f2ae95c-754d-4362-8926-50bb6daff46c
-- statement:
--   Prove that $\sin(2\theta) = \frac {2\tan \theta}{1 + \tan^2 \theta}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2102 (θ : ℝ) : sin (2 * θ) = 2 * tan θ / (1 + tan θ ^ 2)   :=  by sorry
