-- Prove2me | Theorems.Thm_lean_workbook_plus_80617
-- name    : lean_workbook_plus_80617
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/bf1cbf34-039b-4593-835a-67d7f97a6633
-- statement:
--   Prove that equation $a^2 - b^2=ab - 1$ has infinitely many solutions, if $a,b$ are positive integers
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80617 (a b : ℕ) (h₁ : a > 0 ∧ b > 0): ∃ a b, a^2 - b^2 = a*b - 1   :=  by sorry
