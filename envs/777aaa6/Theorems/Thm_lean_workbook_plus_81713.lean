-- Prove2me | Theorems.Thm_lean_workbook_plus_81713
-- name    : lean_workbook_plus_81713
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/6d685cea-02df-44ed-b695-5190b6eedd5f
-- statement:
--   Find the maximal value or supremum of the functions $f(x) = \cos (x + a) + \cos (\sqrt{2}x + b), a, b \in \mathbb{R} $.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81713 (a b : ℝ) : ∀ x : ℝ, cos (x + a) + cos (Real.sqrt 2 * x + b) ≤ 2   :=  by sorry
