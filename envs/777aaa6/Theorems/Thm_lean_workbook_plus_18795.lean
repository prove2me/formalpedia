-- Prove2me | Theorems.Thm_lean_workbook_plus_18795
-- name    : lean_workbook_plus_18795
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/09251a61-e779-4697-90f9-dff600f368b8
-- statement:
--   divisors for 6: 1,2,3,6 $\Rightarrow$ d(6)=4
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18795 :
  ∑ k in (Nat.divisors 6), 1 = 4   :=  by sorry
