-- Prove2me | Theorems.Thm_lean_workbook_plus_678
-- name    : lean_workbook_plus_678
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/367e6999-e0e0-4584-aed1-22181b5e20ea
-- statement:
--   For example, $\sigma(12)=1+2+3+4+6+12=28$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_678 : ∑ k in (Nat.divisors 12), k = 28   :=  by sorry
