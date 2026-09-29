-- Prove2me | Theorems.Thm_lean_workbook_plus_53074
-- name    : lean_workbook_plus_53074
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/4ffb4cab-82ea-44ad-8b3d-c4432d58b85a
-- statement:
--   Let $u_n^r=3+2\cos \frac{2r\pi}{n-1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53074 (n r : ℕ) (hn : 3 ≤ n) (hr : 0 ≤ r ∧ r ≤ n-1) : ∃ k : ℝ, k = 3 + 2 * Real.cos (2 * r * π / (n - 1))   :=  by sorry
