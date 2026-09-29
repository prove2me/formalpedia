-- Prove2me | Theorems.Thm_lean_workbook_plus_50977
-- name    : lean_workbook_plus_50977
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/fdbf4af9-38f0-4224-b59c-a38fc69bdee5
-- statement:
--   Prove that $ |\sin x + \cos x| \leq \sqrt 2 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50977 : ∀ x : ℝ, abs (sin x + cos x) ≤ Real.sqrt 2   :=  by sorry
