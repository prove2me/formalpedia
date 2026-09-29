-- Prove2me | Theorems.Thm_lean_workbook_plus_9414
-- name    : lean_workbook_plus_9414
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/3ee31d99-3a8c-4fce-9e2d-f5fa838596d8
-- statement:
--   Prove $ a_n = \frac {3n}{(n + 1)(n + 2)}a_1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9414 {a : ℕ → ℝ} (a1 : a 0 = 1) (a_rec : ∀ n, a (n + 1) = (3 * (n + 1)) / ((n + 1 + 1) * (n + 1 + 2)) * a 1) : ∀ n, a n = (3 * n) / ((n + 1) * (n + 2)) * a 1   :=  by sorry
