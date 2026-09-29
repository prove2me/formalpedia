-- Prove2me | Theorems.Thm_lean_workbook_plus_72258
-- name    : lean_workbook_plus_72258
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/f77f326a-315d-4f7e-80eb-e62b5606f59a
-- statement:
--   There are $\frac{495}{45} = \boxed{11}$ multiples of $45$ less than $500.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72258 :
  Finset.card (Finset.filter (λ x => 45∣x) (Finset.Ico 45 500)) = 11   :=  by sorry
