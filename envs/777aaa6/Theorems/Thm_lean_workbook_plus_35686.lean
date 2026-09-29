-- Prove2me | Theorems.Thm_lean_workbook_plus_35686
-- name    : lean_workbook_plus_35686
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/2751b600-72a8-441f-8783-f758d403fc0a
-- statement:
--   Prove that the expression $ \frac {(3n)!}{(3!)^n}$ is an integer for all $ n > = 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35686 (n : ℕ) (hn : 0 ≤ n) :
  ∃ k : ℕ, (3 * n)! / (3!)^n = k   :=  by sorry
