-- Prove2me | Theorems.Thm_lean_workbook_plus_46244
-- name    : lean_workbook_plus_46244
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/ece71b2a-e7d0-48e8-b735-63d3009058fc
-- statement:
--   Simplifying further, we get $1-\frac1n<c+d<1+\frac1n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46244 (n : ℕ) (hn : 1 < n) (c d : ℝ) (hcd : c + d = 1) :
  1 - 1 / n < c + d ∧ c + d < 1 + 1 / n   :=  by sorry
