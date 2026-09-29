-- Prove2me | Theorems.Thm_lean_workbook_plus_19388
-- name    : lean_workbook_plus_19388
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/1d9d5b8f-be6d-457b-84bf-8db8ae251018
-- statement:
--   prove that $\sin(-x) = -\sin(x)$ and $\cos(-x) = \cos(x)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19388 : ∀ x : ℝ, sin (-x) = -sin x   :=  by sorry
