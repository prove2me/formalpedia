-- Prove2me | Theorems.Thm_lean_workbook_plus_64522
-- name    : lean_workbook_plus_64522
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/f3b40862-1da5-49a7-8fca-b0f30c6ba2a4
-- statement:
--   Prove that if $p$ is prime, then all numbers in $Z_p$ except $\hat{0}$ are invertible.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64522 (p : ℕ) (hp : p.Prime) (x : ZMod p) (hx : x ≠ 0) : ∃ y, x * y = 1   :=  by sorry
