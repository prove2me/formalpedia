-- Prove2me | Theorems.Thm_lean_workbook_plus_56650
-- name    : lean_workbook_plus_56650
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/64aeba2b-8baf-4404-b44e-e064a0c4df30
-- statement:
--   How do we get $\dbinom{10}{2}\dbinom{4}{2}\dbinom{4}{2}=1620$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56650 :
  (Nat.choose 10 2 * Nat.choose 4 2 * Nat.choose 4 2) = 1620   :=  by sorry
