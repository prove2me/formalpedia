-- Prove2me | Theorems.Thm_lean_workbook_plus_48158
-- name    : lean_workbook_plus_48158
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/c5303cd7-2a80-401d-bf95-4204981015f3
-- statement:
--   Find the general term of the sequence $ 1, \frac {1}{4}, \frac {1}{9}, \frac {1}{16} ...$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48158 (n : ℕ) : ∃ f : ℕ → ℝ, ∀ n, f n = 1 / (n + 1)^2   :=  by sorry
