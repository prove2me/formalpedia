-- Prove2me | Theorems.Thm_lean_workbook_plus_17363
-- name    : lean_workbook_plus_17363
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/da7cc795-111e-43f7-9f2a-210c6c8be7ec
-- statement:
--   Show that for $n \geq 1$ and $1 \leq k \leq n$, $k(n-k+1) \geq n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17363 (n k : ℕ) (h₁ : 1 ≤ k ∧ k ≤ n) : k * (n - k + 1) ≥ n   :=  by sorry
