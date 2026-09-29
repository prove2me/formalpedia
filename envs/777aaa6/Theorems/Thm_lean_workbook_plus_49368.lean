-- Prove2me | Theorems.Thm_lean_workbook_plus_49368
-- name    : lean_workbook_plus_49368
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/cdb407f4-d3b4-4828-85ce-c8d4c49adc8d
-- statement:
--   Find the closed form of the sequence defined by $ a_0=1;a_1=6; a_{n+2}=6a_{n+1}-a_n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49368 (a : ℕ → ℕ) (a0 : a 0 = 1) (a1 : a 1 = 6) (a_rec : ∀ n, a (n + 2) = 6 * a (n + 1) - a n) : ∃ f : ℕ → ℕ, ∀ n, a n = f n   :=  by sorry
