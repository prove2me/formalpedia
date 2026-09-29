-- Prove2me | Theorems.Thm_lean_workbook_plus_18733
-- name    : lean_workbook_plus_18733
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/4e4a403f-1a99-4046-a0a6-7da5a0e69645
-- statement:
--   odd numbers are congruent to $1 \pmod 2$ , and evens are congruent to $0 \pmod 2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18733 : ∀ n : ℤ, n % 2 = 1 ↔ nodd   :=  by sorry
