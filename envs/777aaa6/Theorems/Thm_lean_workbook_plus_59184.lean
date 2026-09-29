-- Prove2me | Theorems.Thm_lean_workbook_plus_59184
-- name    : lean_workbook_plus_59184
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/34065857-d388-4cd0-8991-00d19919cb07
-- statement:
--   If $a$ and $b$ have opposite signs, then $ab < 0$. Provide a proof or a counterexample.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59184    (a b : ℝ)
    (h₁ : a * b < 0)
    : (a > 0 ∧ b < 0) ∨ (a < 0 ∧ b > 0)   :=  by sorry
