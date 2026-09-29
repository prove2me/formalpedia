-- Prove2me | Theorems.Thm_lean_workbook_plus_56573
-- name    : lean_workbook_plus_56573
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/e5a317af-6566-46d1-a514-e2e14997cd58
-- statement:
--   $ S\equiv 0+0+\cdots+0\equiv 0\pmod{a}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56573 :
  ∀ (a : ℕ), (a > 0) → (∑ x in Finset.range a, 0) % a = 0   :=  by sorry
