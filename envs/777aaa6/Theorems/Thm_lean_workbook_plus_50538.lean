-- Prove2me | Theorems.Thm_lean_workbook_plus_50538
-- name    : lean_workbook_plus_50538
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/324c86ec-6f93-4195-98ae-f24a385366f5
-- statement:
--   We have $\dfrac {(n-1)^2} {n!} = \dfrac {1} {n!} - \dfrac {1} {(n-1)!} + \dfrac {1} {(n-2)!}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50538 : ∀ n : ℕ, ((n - 1) ^ 2 / n!) = 1 / n! - 1 / (n - 1)! + 1 / (n - 2)!   :=  by sorry
