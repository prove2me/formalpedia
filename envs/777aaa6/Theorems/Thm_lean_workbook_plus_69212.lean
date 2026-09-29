-- Prove2me | Theorems.Thm_lean_workbook_plus_69212
-- name    : lean_workbook_plus_69212
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/32b6bc76-eb91-4d36-aec8-d8e53c567fe4
-- statement:
--   Find the recursive formula for the number of sit-ups Rambo will do on day $n$, given that he starts with 24 sit-ups and adds 3 sit-ups each day.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69212 (f : ℕ → ℕ) (h₁ : f 0 = 24) (h₂ : ∀ n, f (n + 1) = f n + 3) : ∀ n, f n = 24 + 3 * n   :=  by sorry
