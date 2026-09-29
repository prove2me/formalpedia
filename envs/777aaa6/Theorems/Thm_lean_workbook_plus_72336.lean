-- Prove2me | Theorems.Thm_lean_workbook_plus_72336
-- name    : lean_workbook_plus_72336
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/4367ff80-d740-44ae-81cc-4de6c6d74a6d
-- statement:
--   If $x$ is a perfect square, then $x^n$ will be a perfect square no matter what n is.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72336 (x : ℕ) (n : ℕ) (hx : ∃ t, t^2 = x) : ∃ t, t^2 = x^n   :=  by sorry
