-- Prove2me | Theorems.Thm_lean_workbook_plus_56030
-- name    : lean_workbook_plus_56030
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/bd19fe73-d2c3-4e52-bafc-aa471ff15c3e
-- statement:
--   $S_{0}= 2$ $S_{k+1}= S_{1}S_{k}-S_{k-1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56030 (n : ℕ) : ∃ (f : ℕ → ℕ), f 0 = 2 ∧ ∀ k, f (k + 1) = f 1 * f k - f (k - 1)   :=  by sorry
