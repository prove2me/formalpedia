-- Prove2me | Theorems.Thm_lean_workbook_plus_3575
-- name    : lean_workbook_plus_3575
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/794c0d3c-a9d4-4496-84b6-933fbca7bcc2
-- statement:
--   Every number can be written as either $\{0, 1, \ldots, 7\} \mod 8$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3575 (n : ℤ) : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7   :=  by sorry
