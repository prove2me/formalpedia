-- Prove2me | Theorems.Thm_lean_workbook_plus_26984
-- name    : lean_workbook_plus_26984
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/fbc5955e-ed3f-42e6-8572-2fbf7d03fb6a
-- statement:
--   In order to calculate $2009^5$ , $2009^{25}$ and $2009^{125}$ , one can use the previous results: $2009^5 = 2009^4 \cdot 2009^1$ , $2009^{25} = 2009^{20} \cdot 2009^5$ and $2009^{125} = 2009^{100} \cdot 2009^{25}$ . Again, one multiplication and division and we're done.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26984 :
  2009^5 = 2009^4 * 2009^1 ∧ 2009^25 = 2009^20 * 2009^5 ∧ 2009^125 = 2009^100 * 2009^25   :=  by sorry
