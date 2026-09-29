-- Prove2me | Theorems.Thm_lean_workbook_plus_30327
-- name    : lean_workbook_plus_30327
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/ad70ee5c-431b-46a8-9ff5-e1fbd9ee8f4d
-- statement:
--   (b) Show that $a_n<3$ for all natural $n$ : straightforward induction
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30327 (a : ℕ → ℝ) (a0 : a 0 = 2) (a_rec : ∀ n, a (n + 1) = 2 + a n / 2) : ∀ n, a n < 3   :=  by sorry
